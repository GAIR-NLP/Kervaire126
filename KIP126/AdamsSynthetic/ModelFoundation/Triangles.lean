module

public import KIP126.AdamsSynthetic.ModelFoundation.Suspension
public import KIP126.AdamsSynthetic.ModelFoundation.ArrowLocalization
public import Mathlib.CategoryTheory.Triangulated.Basic

/-! Triangles formed from the model cofiber and derived-suspension shift.
Their isomorphism-closed class satisfies triangle existence,
the contractible case, and completion of squares. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
open CategoryTheory.Functor HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

section WithShift
variable [HasShift H ℤ] (σ : shiftFunctor H (1 : ℤ) ≅ G.derivedSuspensionFunctor L)

/-- The actual derived boundary expressed in the integer shift constructed
from the same derived suspension. -/
noncomputable def shiftedCofiberBoundaryWithShift :
    G.cofiberFunctor ⋙ L ⟶ Arrow.leftFunc ⋙ L ⋙ shiftFunctor H (1 : ℤ) :=
  G.localizedCofiberBoundary L ≫
    whiskerLeft (Arrow.leftFunc ⋙ L) σ.inv

/-- Each actual arrow yields a triangle using its actual model cofiber. -/
noncomputable def modelCofiberTriangleWithShift (f : Arrow C) : Triangle H :=
  Triangle.mk (L.map f.hom) ((G.localizedCofiberInclusion L).app f)
    ((G.shiftedCofiberBoundaryWithShift L σ).app f)

/-- The actual cofiber triangles vary functorially with strict point-set squares. -/
noncomputable def modelCofiberTriangleFunctorWithShift : Arrow C ⥤ Triangle H where
  obj := G.modelCofiberTriangleWithShift L σ
  map {f g} φ :=
    { hom₁ := L.map φ.left
      hom₂ := L.map φ.right
      hom₃ := L.map (G.cofiberFunctor.map φ)
      comm₁ := by
        change L.map f.hom ≫ L.map φ.right = L.map φ.left ≫ L.map g.hom
        simpa only [← L.map_comp] using congrArg L.map φ.w.symm
      comm₂ := ((G.localizedCofiberInclusion L).naturality φ).symm
      comm₃ := by
        exact ((G.shiftedCofiberBoundaryWithShift L σ).naturality φ).symm }
  map_id f := by ext <;> simp [modelCofiberTriangleWithShift]
  map_comp φ ψ := by ext <;> simp

/-- Objectwise weak equivalences induce isomorphisms of the actual triangles. -/
theorem modelCofiberTriangleFunctor_invertsWithShift :
    (weakEquivalences C).arrow.IsInvertedBy (G.modelCofiberTriangleFunctorWithShift L σ) := by
  intro f g φ hφ
  apply Triangle.isIso_of_isIsos
  · exact Localization.inverts L (weakEquivalences C) _ hφ.1
  · exact Localization.inverts L (weakEquivalences C) _ hφ.2
  · exact Localization.inverts L (weakEquivalences C) _
      (G.cofiberFunctor_weakEquivalences φ hφ)

/-- A genuine triangle-valued functor on the localization of actual arrows. -/
noncomputable def derivedCofiberTriangleFunctorWithShift :
    (weakEquivalences C).arrow.Localization ⥤ Triangle H :=
  Localization.lift (G.modelCofiberTriangleFunctorWithShift L σ)
    (G.modelCofiberTriangleFunctor_invertsWithShift L σ) (weakEquivalences C).arrow.Q

/-- The isomorphism-closed class of model cofiber triangles. -/
def modelCofiberTrianglesWithShift : Set (Triangle H) :=
  { T | ∃ f : Arrow C, Nonempty (T ≅ G.modelCofiberTriangleWithShift L σ f) }

theorem modelCofiberTriangles_isomorphicWithShift (T₁ T₂ : Triangle H)
    (h : T₁ ∈ G.modelCofiberTrianglesWithShift L σ) (e : T₂ ≅ T₁) :
    T₂ ∈ G.modelCofiberTrianglesWithShift L σ := by
  obtain ⟨f, ⟨ef⟩⟩ := h
  exact ⟨f, ⟨e ≪≫ ef⟩⟩

omit [HasZeroMorphisms C] [HasZeroObject C] [HasShift H ℤ] in
private theorem modelLocalization_mapArrow_essSurj : L.mapArrow.EssSurj := by
  letI : (BifibrantObject.ι ⋙ L).Full := Functor.Full.of_iso
    (Localization.compUniqFunctor BifibrantObject.toHoCat (BifibrantObject.ι ⋙ L)
      (weakEquivalences (BifibrantObject C)))
  letI := Localization.essSurj (BifibrantObject.ι ⋙ L)
    (weakEquivalences (BifibrantObject C))
  refine ⟨fun f => ?_⟩
  obtain ⟨g, ⟨e⟩⟩ :=
    (inferInstance : (BifibrantObject.ι ⋙ L).mapArrow.EssSurj).mem_essImage f
  exact ⟨BifibrantObject.ι.mapArrow.obj g, ⟨e⟩⟩

/-- Every arrow of the localization occurs as the first map of a triangle
in the actual model class. -/
theorem modelCofiberTriangles_coconeWithShift {X Y : H} (f : X ⟶ Y) :
    ∃ (Z : H) (g : Y ⟶ Z) (h : Z ⟶ (shiftFunctor H (1 : ℤ)).obj X),
      Triangle.mk f g h ∈ G.modelCofiberTrianglesWithShift L σ := by
  letI := modelLocalization_mapArrow_essSurj L
  obtain ⟨a, ⟨e⟩⟩ := (inferInstance : L.mapArrow.EssSurj).mem_essImage (Arrow.mk f)
  let T := G.modelCofiberTriangleWithShift L σ a
  refine ⟨T.obj₃, e.inv.right ≫ T.mor₂,
    T.mor₃ ≫ (shiftFunctor H (1 : ℤ)).map e.hom.left, a, ⟨?_⟩⟩
  refine Triangle.isoMk _ T (Arrow.leftFunc.mapIso e.symm)
    (Arrow.rightFunc.mapIso e.symm) (Iso.refl _) ?_ ?_ ?_
  · exact e.inv.w.symm
  · simp
  · dsimp [T, modelCofiberTriangleWithShift]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
    have h : e.hom.left ≫ e.inv.left = 𝟙 _ := by
      exact congrArg (fun φ => φ.left) e.hom_inv_id
    erw [h, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- The contractible triangle belongs to the actual model class. -/
theorem modelCofiberTriangles_contractibleWithShift [HasZeroMorphisms H] [HasZeroObject H]
    (X : H) : contractibleTriangle X ∈ G.modelCofiberTrianglesWithShift L σ := by
  letI := Localization.essSurj L (weakEquivalences C)
  let Y := L.objPreimage X
  let e : L.obj Y ≅ X := L.objObjPreimageIso X
  let T := G.modelCofiberTriangleWithShift L σ (Arrow.mk (𝟙 Y))
  have hzero : IsZero T.obj₃ := G.localizedCofiberIdentity_isZero L Y
  refine ⟨Arrow.mk (𝟙 Y), ⟨Iso.symm ?_⟩⟩
  refine Triangle.isoMk T (contractibleTriangle X) e e hzero.isoZero ?_ ?_ ?_
  · simp [T, modelCofiberTriangleWithShift]
  · exact (isZero_zero H).eq_of_tgt _ _
  · exact hzero.eq_of_src _ _


/-- Forgetting the third object retains the actual first-arrow square. -/
def triangleFirstArrowFunctor : Triangle H ⥤ Arrow H where
  obj T := Arrow.mk T.mor₁
  map φ := Arrow.homMk φ.hom₁ φ.hom₂ φ.comm₁.symm
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def modelTriangleFirstArrowComparison :
    G.modelCofiberTriangleFunctorWithShift L σ ⋙ triangleFirstArrowFunctor ≅ L.mapArrow :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro f g φ; ext <;> simp
    [triangleFirstArrowFunctor, modelCofiberTriangleFunctorWithShift])

/-- The derived triangle functor retains a full first-arrow comparison. -/
lemma derivedTriangle_firstArrow_full :
    (G.derivedCofiberTriangleFunctorWithShift L σ ⋙ triangleFirstArrowFunctor).Full := by
  let Q := (weakEquivalences C).arrow.Q
  let eT : Q ⋙ G.derivedCofiberTriangleFunctorWithShift L σ ≅ G.modelCofiberTriangleFunctorWithShift L σ :=
    Localization.fac (G.modelCofiberTriangleFunctorWithShift L σ)
      (G.modelCofiberTriangleFunctor_invertsWithShift L σ) Q
  let e : G.derivedCofiberTriangleFunctorWithShift L σ ⋙ triangleFirstArrowFunctor ≅
      ModelFoundation.derivedArrowFunctor L :=
    (Localization.fullyFaithfulWhiskeringLeft Q (weakEquivalences C).arrow (Arrow H)).preimageIso
      (isoWhiskerRight eT triangleFirstArrowFunctor ≪≫
        G.modelTriangleFirstArrowComparison L σ ≪≫
          (ModelFoundation.derivedArrowComparison L).symm)
  letI := ModelFoundation.derivedArrowFunctor_full L
  exact Functor.Full.of_iso e.symm

/-- Every commutative square between two actual model triangles extends to
 a morphism of those same triangles. -/
lemma modelTriangle_square_completion (f g : Arrow C)
    (φ : triangleFirstArrowFunctor.obj (G.modelCofiberTriangleWithShift L σ f) ⟶
      triangleFirstArrowFunctor.obj (G.modelCofiberTriangleWithShift L σ g)) :
    ∃ ψ : G.modelCofiberTriangleWithShift L σ f ⟶ G.modelCofiberTriangleWithShift L σ g,
      triangleFirstArrowFunctor.map ψ = φ := by
  let Q := (weakEquivalences C).arrow.Q
  let D := G.derivedCofiberTriangleFunctorWithShift L σ
  let U := triangleFirstArrowFunctor (H := H)
  let e : Q ⋙ D ≅ G.modelCofiberTriangleFunctorWithShift L σ :=
    Localization.fac (G.modelCofiberTriangleFunctorWithShift L σ)
      (G.modelCofiberTriangleFunctor_invertsWithShift L σ) Q
  letI := G.derivedTriangle_firstArrow_full L σ
  obtain ⟨q, hq⟩ := (D ⋙ U).map_surjective
    (U.map (e.hom.app f) ≫ φ ≫ U.map (e.inv.app g))
  refine ⟨e.inv.app f ≫ D.map q ≫ e.hom.app g, ?_⟩
  change U.map (e.inv.app f ≫ D.map q ≫ e.hom.app g) = φ
  rw [U.map_comp, U.map_comp]
  change U.map (e.inv.app f) ≫ (D ⋙ U).map q ≫ U.map (e.hom.app g) = φ
  rw [hq]
  change (U.mapIso (e.app f)).inv ≫
    ((U.mapIso (e.app f)).hom ≫ φ ≫ (U.mapIso (e.app g)).inv) ≫
      (U.mapIso (e.app g)).hom = φ
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- TR3 for the isomorphism-closed class of actual model cofiber triangles.
The third component is obtained from the genuine localized arrow lift. -/
theorem modelCofiberTriangles_complete_morphismWithShift
    (T₁ T₂ : Triangle H)
    (h₁ : T₁ ∈ G.modelCofiberTrianglesWithShift L σ)
    (h₂ : T₂ ∈ G.modelCofiberTrianglesWithShift L σ)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
        T₁.mor₃ ≫ (shiftFunctor H (1 : ℤ)).map a = c ≫ T₂.mor₃ := by
  obtain ⟨f, ⟨ef⟩⟩ := h₁
  obtain ⟨g, ⟨eg⟩⟩ := h₂
  let U := triangleFirstArrowFunctor (H := H)
  let φ : U.obj T₁ ⟶ U.obj T₂ := Arrow.homMk a b comm.symm
  obtain ⟨ψ, hψ⟩ := G.modelTriangle_square_completion L σ f g
    (U.map ef.inv ≫ φ ≫ U.map eg.hom)
  let θ : T₁ ⟶ T₂ := ef.hom ≫ ψ ≫ eg.inv
  have hθ : U.map θ = φ := by
    change U.map (ef.hom ≫ ψ ≫ eg.inv) = φ
    rw [U.map_comp, U.map_comp, hψ]
    change (U.mapIso ef).hom ≫
      ((U.mapIso ef).inv ≫ φ ≫ (U.mapIso eg).hom) ≫ (U.mapIso eg).inv = φ
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hθ₁ : θ.hom₁ = a := congrArg Arrow.Hom.left hθ
  have hθ₂ : θ.hom₂ = b := congrArg Arrow.Hom.right hθ
  refine ⟨θ.hom₃, ?_, ?_⟩
  · rw [← hθ₂]
    exact θ.comm₂
  · rw [← hθ₁]
    exact θ.comm₃


end WithShift

variable [(G.derivedSuspensionFunctor L).IsEquivalence]

/-- The actual model triangle functor, in the integer shift derived from the
same model suspension. -/
public noncomputable def modelCofiberTriangleFunctor :
    letI := G.derivedSuspensionHasShift L
    Arrow C ⥤ Triangle H := by
  letI := G.derivedSuspensionHasShift L
  let δ : G.cofiberFunctor ⋙ L ⟶ Arrow.leftFunc ⋙ L ⋙ shiftFunctor H (1 : ℤ) :=
    G.localizedCofiberBoundary L ≫
      whiskerLeft (Arrow.leftFunc ⋙ L) (G.derivedSuspensionShiftOneIso L).inv
  exact
    { obj := fun f => Triangle.mk (L.map f.hom)
        ((G.localizedCofiberInclusion L).app f) (δ.app f)
      map := fun {f g} φ =>
        { hom₁ := L.map φ.left
          hom₂ := L.map φ.right
          hom₃ := L.map (G.cofiberFunctor.map φ)
          comm₁ := by
            change L.map f.hom ≫ L.map φ.right = L.map φ.left ≫ L.map g.hom
            simpa only [← L.map_comp] using congrArg L.map φ.w.symm
          comm₂ := ((G.localizedCofiberInclusion L).naturality φ).symm
          comm₃ := (δ.naturality φ).symm }
      map_id := by intro f; ext <;> simp
      map_comp := by intro f g h φ ψ; ext <;> simp }

/-- This actual triangle functor descends to localized actual arrows. -/
public noncomputable def derivedCofiberTriangleFunctor :
    letI := G.derivedSuspensionHasShift L
    (weakEquivalences C).arrow.Localization ⥤ Triangle H := by
  letI := G.derivedSuspensionHasShift L
  exact Localization.lift (G.modelCofiberTriangleFunctor L)
    (show (weakEquivalences C).arrow.IsInvertedBy (G.modelCofiberTriangleFunctor L) from by
      exact G.modelCofiberTriangleFunctor_invertsWithShift L
        (G.derivedSuspensionShiftOneIso L)) (weakEquivalences C).arrow.Q

/-- The isomorphism closure of the actual model triangles with their actual
model-derived shift. -/
public noncomputable def modelCofiberTriangles :
    letI := G.derivedSuspensionHasShift L
    Set (Triangle H) := by
  letI := G.derivedSuspensionHasShift L
  exact { T | ∃ f : Arrow C, Nonempty (T ≅ (G.modelCofiberTriangleFunctor L).obj f) }

/-- The specified actual model class is closed under isomorphisms. -/
public theorem modelCofiberTriangles_isomorphic :
    letI := G.derivedSuspensionHasShift L
    ∀ (T₁ T₂ : Triangle H), T₁ ∈ G.modelCofiberTriangles L →
      (T₂ ≅ T₁) → T₂ ∈ G.modelCofiberTriangles L := by
  letI := G.derivedSuspensionHasShift L
  exact G.modelCofiberTriangles_isomorphicWithShift L (G.derivedSuspensionShiftOneIso L)

/-- Every morphism of the specified localization extends to an actual model
cofiber triangle. No pretriangulated structure is assumed. -/
public theorem modelCofiberTriangles_cocone :
    letI := G.derivedSuspensionHasShift L
    ∀ {X Y : H} (f : X ⟶ Y),
      ∃ (Z : H) (g : Y ⟶ Z) (h : Z ⟶ (shiftFunctor H (1 : ℤ)).obj X),
        Triangle.mk f g h ∈ G.modelCofiberTriangles L := by
  letI := G.derivedSuspensionHasShift L
  intro X Y f
  exact G.modelCofiberTriangles_coconeWithShift L (G.derivedSuspensionShiftOneIso L) f

/-- Contractible triangles lie in the specified model class. -/
public theorem modelCofiberTriangles_contractible
    [HasZeroMorphisms H] [HasZeroObject H] :
    letI := G.derivedSuspensionHasShift L
    ∀ X : H, contractibleTriangle X ∈ G.modelCofiberTriangles L := by
  letI := G.derivedSuspensionHasShift L
  exact G.modelCofiberTriangles_contractibleWithShift L (G.derivedSuspensionShiftOneIso L)

/-- Every commutative square in the first two positions of actual model
cofiber triangles extends to a morphism of those same triangles. -/
public theorem modelCofiberTriangles_complete_morphism :
    letI := G.derivedSuspensionHasShift L
    ∀ (T₁ T₂ : Triangle H),
      T₁ ∈ G.modelCofiberTriangles L → T₂ ∈ G.modelCofiberTriangles L →
      ∀ (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
        T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
        ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
          T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
            T₁.mor₃ ≫ (shiftFunctor H (1 : ℤ)).map a = c ≫ T₂.mor₃ := by
  letI := G.derivedSuspensionHasShift L
  exact G.modelCofiberTriangles_complete_morphismWithShift L (G.derivedSuspensionShiftOneIso L)


end KIP126.StableHomotopy.CofibrantGeneration
