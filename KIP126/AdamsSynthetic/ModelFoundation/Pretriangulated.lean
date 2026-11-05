module

public import KIP126.AdamsSynthetic.ModelFoundation.Preadditive
public import KIP126.AdamsSynthetic.ModelFoundation.Triangles
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all KIP126.AdamsSynthetic.ModelFoundation.Rotation
import all KIP126.AdamsSynthetic.ModelFoundation.Triangles
public import Mathlib.CategoryTheory.Yoneda

/-! The pretriangulation of a pointed cofibrantly generated stable model.
All operations use the actual cofiber, boundary, and suspension constructed in
this module. Additivity, both directions of rotation, and triangle completion
follow from the model structure. No pretriangulated structure on the target
is an input. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.WeakTriangleRotation
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
variable (D : Set (Triangle C))
  (hcontract : ∀ X : C, contractibleTriangle X ∈ D)
  (hrotate : ∀ T : Triangle C, T ∈ D → T.rotate ∈ D)
  (hTR3 : ∀ (T U : Triangle C), T ∈ D → U ∈ D →
    ∀ (a : T.obj₁ ⟶ U.obj₁) (b : T.obj₂ ⟶ U.obj₂),
      T.mor₁ ≫ b = a ≫ U.mor₁ →
      ∃ c : T.obj₃ ⟶ U.obj₃, T.mor₂ ≫ c = b ≫ U.mor₂ ∧
        T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ U.mor₃)

omit [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hcontract hTR3 in
private theorem comp_zero12 (T : Triangle C) (hT : T ∈ D) :
    T.mor₁ ≫ T.mor₂ = 0 := by
  obtain ⟨c, hc, _⟩ := hTR3 _ _ (hcontract T.obj₁) hT (𝟙 T.obj₁) T.mor₁ rfl
  simpa only [contractibleTriangle_mor₂, zero_comp] using hc.symm

omit [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hcontract hrotate hTR3 in
private theorem comp_zero23 (T : Triangle C) (hT : T ∈ D) :
    T.mor₂ ≫ T.mor₃ = 0 :=
  comp_zero12 D hcontract hTR3 T.rotate (hrotate T hT)

omit [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hcontract hrotate hTR3 in
private theorem comp_zero31 (T : Triangle C) (hT : T ∈ D) :
    T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
  simpa using comp_zero12 D hcontract hTR3 T.rotate.rotate
    (hrotate _ (hrotate _ hT))

omit [HasZeroObject C] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hrotate hTR3 in
private theorem complete_morphism12 (T U : Triangle C) (hT : T ∈ D) (hU : U ∈ D)
    (b : T.obj₂ ⟶ U.obj₂) (c : T.obj₃ ⟶ U.obj₃)
    (comm : T.mor₂ ≫ c = b ≫ U.mor₂) :
    ∃ a : T.obj₁ ⟶ U.obj₁, T.mor₁ ≫ b = a ≫ U.mor₁ ∧
      T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ U.mor₃ := by
  obtain ⟨a, ha₁, ha₂⟩ := hTR3 _ _ (hrotate _ hT) (hrotate _ hU) b c comm
  refine ⟨(shiftFunctor C (1 : ℤ)).preimage a, ?_, ?_⟩
  · apply (shiftFunctor C (1 : ℤ)).map_injective
    dsimp at ha₂
    rw [neg_comp, comp_neg, neg_inj] at ha₂
    simpa only [Functor.map_comp, Functor.map_preimage] using! ha₂
  · simpa only [Functor.map_preimage] using! ha₁

omit [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hcontract hrotate hTR3 in
private theorem hom_exact2 (T : Triangle C) (hT : T ∈ D)
    {W : C} (f : W ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) :
    ∃ g : W ⟶ T.obj₁, f = g ≫ T.mor₁ := by
  obtain ⟨g, hg, _⟩ := complete_morphism12 D hrotate hTR3 _ T
    (hcontract W) hT f 0 (by simpa using hf.symm)
  exact ⟨g, by simpa using hg⟩

omit [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hcontract hrotate hTR3 in
private theorem hom_exact3 (T : Triangle C) (hT : T ∈ D)
    {W : C} (f : W ⟶ T.obj₃) (hf : f ≫ T.mor₃ = 0) :
    ∃ g : W ⟶ T.obj₂, f = g ≫ T.mor₂ :=
  hom_exact2 D hcontract hrotate hTR3 _ (hrotate _ hT) f hf

omit [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hcontract hrotate hTR3 in
private theorem hom_exact1 (T : Triangle C) (hT : T ∈ D)
    {W : C} (f : W ⟶ T.obj₁⟦(1 : ℤ)⟧) (hf : f ≫ T.mor₁⟦(1 : ℤ)⟧' = 0) :
    ∃ g : W ⟶ T.obj₃, f = g ≫ T.mor₃ :=
  hom_exact2 D hcontract hrotate hTR3 _ (hrotate _ (hrotate _ hT)) f (by
    simpa using hf)

omit [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
include hcontract hrotate hTR3 in
private theorem isIso3_of_isIso12 {T U : Triangle C} (φ : T ⟶ U)
    (hT : T ∈ D) (hU : U ∈ D) (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) :
    IsIso φ.hom₃ := by
  have : Mono φ.hom₃ := by
    rw [mono_iff_cancel_zero]
    intro W a ha
    obtain ⟨b, rfl⟩ := hom_exact3 D hcontract hrotate hTR3 T hT a (by
      rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), assoc, φ.comm₃,
        reassoc_of% ha, zero_comp, zero_comp])
    have hb : (b ≫ φ.hom₂) ≫ U.mor₂ = 0 := by
      rw [assoc, ← φ.comm₂, ← assoc, ha]
    obtain ⟨d, hd⟩ := hom_exact2 D hcontract hrotate hTR3 U hU (b ≫ φ.hom₂) hb
    have hb' : b = (d ≫ inv φ.hom₁) ≫ T.mor₁ := by
      apply (cancel_mono φ.hom₂).1
      rw [assoc, assoc, φ.comm₁, IsIso.inv_hom_id_assoc]
      exact hd
    rw [hb', assoc, comp_zero12 D hcontract hTR3 T hT, comp_zero]
  refine isIso_of_yoneda_map_bijective _ (fun W => ⟨?_, ?_⟩)
  · intro a b h
    exact (cancel_mono φ.hom₃).1 h
  · intro y
    obtain ⟨z, hz⟩ : ∃ z : W ⟶ T.obj₁⟦(1 : ℤ)⟧,
        z ≫ φ.hom₁⟦(1 : ℤ)⟧' = y ≫ U.mor₃ :=
      ⟨y ≫ U.mor₃ ≫ inv (φ.hom₁⟦(1 : ℤ)⟧'), by simp⟩
    have hz0 : z ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      rw [← cancel_mono (φ.hom₂⟦(1 : ℤ)⟧'), assoc, zero_comp,
        ← Functor.map_comp, φ.comm₁, Functor.map_comp, ← assoc, hz, assoc,
        comp_zero31 D hcontract hrotate hTR3 U hU, comp_zero]
    obtain ⟨x, hx⟩ := hom_exact1 D hcontract hrotate hTR3 T hT z hz0
    have hz' : (x ≫ φ.hom₃) ≫ U.mor₃ = y ≫ U.mor₃ := by
      rw [assoc, ← φ.comm₃, ← assoc, ← hx, hz]
    obtain ⟨b, hb⟩ := hom_exact3 D hcontract hrotate hTR3 U hU (y - x ≫ φ.hom₃)
      (by rw [sub_comp, hz', sub_self])
    refine ⟨x + (b ≫ inv φ.hom₂) ≫ T.mor₂, ?_⟩
    dsimp
    rw [add_comp, assoc, assoc, φ.comm₂, IsIso.inv_hom_id_assoc, ← hb,
      add_sub_cancel]

include hcontract hrotate hTR3 in
private theorem rotate_iff
    (hiso : ∀ T ∈ D, ∀ U : Triangle C, (U ≅ T) → U ∈ D)
    (hcocone : ∀ {X Y : C} (f : X ⟶ Y),
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ D)
    (T : Triangle C) : T ∈ D ↔ T.rotate ∈ D := by
  refine ⟨hrotate T, ?_⟩
  intro hRT
  let V := T.invRotate
  obtain ⟨Z, g, h, hU⟩ := hcocone V.mor₁
  let U : Triangle C := Triangle.mk V.mor₁ g h
  change U ∈ D at hU
  have hRU : U.rotate.rotate.rotate ∈ D := hrotate _ (hrotate _ (hrotate _ hU))
  have hRV : V.rotate.rotate.rotate ∈ D := by
    apply hiso T.rotate.rotate (hrotate _ hRT) V.rotate.rotate.rotate
    exact (rotate C ⋙ rotate C).mapIso (invRotCompRot.app T)
  have comm : U.rotate.rotate.rotate.mor₁ ≫ 𝟙 V.rotate.rotate.rotate.obj₂ =
      𝟙 U.rotate.rotate.rotate.obj₁ ≫ V.rotate.rotate.rotate.mor₁ := by
    simp [U, Triangle.rotate]
  obtain ⟨c, hc₂, hc₃⟩ := hTR3 _ _ hRU hRV (𝟙 _) (𝟙 _) comm
  let φ : U.rotate.rotate.rotate ⟶ V.rotate.rotate.rotate :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := c
      comm₁ := comm
      comm₂ := hc₂
      comm₃ := hc₃ }
  haveI : IsIso φ.hom₁ := inferInstanceAs (IsIso (𝟙 _))
  haveI : IsIso φ.hom₂ := inferInstanceAs (IsIso (𝟙 _))
  haveI : IsIso φ.hom₃ := isIso3_of_isIso12 D hcontract hrotate hTR3 φ hRU hRV
    inferInstance inferInstance
  haveI : IsIso φ := Triangle.isIso_of_isIsos φ inferInstance inferInstance inferInstance
  let e : U ≅ V := (rotate C ⋙ rotate C ⋙ rotate C).preimageIso (asIso φ)
  have hV : V ∈ D := hiso U hU V e.symm
  exact hiso V.rotate (hrotate _ hV) T (invRotCompRot.app T).symm



end KIP126.StableHomotopy.WeakTriangleRotation
end

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]
  [(G.derivedSuspensionFunctor L).IsEquivalence]
noncomputable section

/-- The pretriangulation is constructed from the same actual model cofiber,
boundary, and suspension. Its only stability premise is invertibility of that
actual derived suspension. -/
@[implicit_reducible, no_expose]
public def modelPretriangulated :
    letI := G.modelPreadditive L;
    letI := G.derivedSuspensionHasShift L;
    letI := localization_hasZeroObject L (weakEquivalences C);
    letI : ∀ n : ℤ, (shiftFunctor H n).Additive := G.modelShiftAdditive L;
    Pretriangulated H := by
  letI := G.modelPreadditive L
  letI := G.derivedSuspensionHasShift L
  letI := localization_hasZeroObject L (weakEquivalences C)
  letI : ∀ n : ℤ, (shiftFunctor H n).Additive := G.modelShiftAdditive L
  let σ := G.derivedSuspensionShiftOneIso L
  let D := G.modelCofiberTrianglesWithShift L σ
  have hcontract := G.modelCofiberTriangles_contractibleWithShift L σ
  have hrotate := G.modelCofiberTriangles_rotateWithShift L σ
  have hTR3 := G.modelCofiberTriangles_complete_morphismWithShift L σ
  have hiso : ∀ T ∈ D, ∀ U, (U ≅ T) → U ∈ D := by
    intro T hT U e
    exact G.modelCofiberTriangles_isomorphicWithShift L σ T U hT e
  have hcocone {X Y : H} (f : X ⟶ Y) := G.modelCofiberTriangles_coconeWithShift L σ f
  exact {
    distinguishedTriangles := D
    isomorphic_distinguished := hiso
    contractible_distinguished := hcontract
    distinguished_cocone_triangle := hcocone
    rotate_distinguished_triangle :=
      WeakTriangleRotation.rotate_iff D hcontract hrotate hTR3 hiso hcocone
    complete_distinguished_triangle_morphism := hTR3 }


/-- The distinguished triangles are the model cofiber triangles, with their boundary
maps. -/
public theorem modelPretriangulated_distinguished :
    letI := G.modelPreadditive L;
    letI := G.derivedSuspensionHasShift L;
    letI := localization_hasZeroObject L (weakEquivalences C);
    letI : ∀ n : ℤ, (shiftFunctor H n).Additive := G.modelShiftAdditive L;
    letI := G.modelPretriangulated L;
    distTriang H = G.modelCofiberTriangles L := by
  rfl

end
end KIP126.StableHomotopy.CofibrantGeneration
