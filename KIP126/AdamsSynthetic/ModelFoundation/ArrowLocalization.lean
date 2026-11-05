module
public import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy
public import Mathlib.CategoryTheory.Comma.Arrow

/-! The comparison from localized point-set arrows to arrows of the homotopy
category is full, using bifibrant replacements and homotopy lifting. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.ModelFoundation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

lemma bifibrantLocalization_full : (BifibrantObject.ι ⋙ L).Full := by
  exact Functor.Full.of_iso (Localization.compUniqFunctor
    BifibrantObject.toHoCat (BifibrantObject.ι ⋙ L)
    (weakEquivalences (BifibrantObject C)))

lemma localization_map_eq_leftHomotopy {X Y : C}
    [IsCofibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y]
    (f g : X ⟶ Y) (h : L.map f = L.map g) : LeftHomotopyRel f g := by
  let f' : BifibrantObject.mk X ⟶ BifibrantObject.mk Y := BifibrantObject.homMk f
  let g' : BifibrantObject.mk X ⟶ BifibrantObject.mk Y := BifibrantObject.homMk g
  let e := Localization.compUniqFunctor (BifibrantObject.ι ⋙ L)
    BifibrantObject.toHoCat (weakEquivalences (BifibrantObject C))
  have h' : BifibrantObject.toHoCat.map f' = BifibrantObject.toHoCat.map g' := by
    apply (cancel_epi (e.hom.app (BifibrantObject.mk X))).1
    rw [← e.hom.naturality, ← e.hom.naturality]
    change (Localization.uniq (BifibrantObject.ι ⋙ L) BifibrantObject.toHoCat
      (weakEquivalences (BifibrantObject C))).functor.map (L.map f) ≫ _ =
      (Localization.uniq (BifibrantObject.ι ⋙ L) BifibrantObject.toHoCat
      (weakEquivalences (BifibrantObject C))).functor.map (L.map g) ≫ _
    rw [h]
  exact BifibrantObject.homRel_iff_leftHomotopyRel.mp
    ((BifibrantObject.toHoCat_map_eq_iff f' g').mp h')

/-- A homotopy commutative square with bifibrant endpoints and a fibration
on the target can be represented by a strictly commutative square. -/
lemma strictify_square {f g : Arrow C}
    [IsCofibrant f.left] [IsFibrant f.left]
    [IsCofibrant f.right] [IsFibrant f.right]
    [IsCofibrant g.left] [IsFibrant g.left]
    [IsCofibrant g.right] [IsFibrant g.right] [Fibration g.hom]
    (φ : L.mapArrow.obj f ⟶ L.mapArrow.obj g) :
    ∃ ψ : f ⟶ g, L.mapArrow.map ψ = φ := by
  letI := bifibrantLocalization_full L
  obtain ⟨a, ha⟩ := (BifibrantObject.ι ⋙ L).map_surjective
    (X := BifibrantObject.mk f.left) (Y := BifibrantObject.mk g.left) φ.left
  obtain ⟨b, hb⟩ := (BifibrantObject.ι ⋙ L).map_surjective
    (X := BifibrantObject.mk f.right) (Y := BifibrantObject.mk g.right) φ.right
  change L.map a.hom = φ.left at ha
  change L.map b.hom = φ.right at hb
  have heq : L.map (a.hom ≫ g.hom) = L.map (f.hom ≫ b.hom) := by
    rw [L.map_comp, L.map_comp, ha, hb]
    exact φ.w
  have hhom := localization_map_eq_leftHomotopy L _ _ heq
  obtain ⟨P, hP, ⟨h⟩⟩ := hhom.exists_good_cylinder
  letI := hP
  obtain ⟨a', h', hh⟩ := h.covering_homotopy g.hom a.hom rfl
  have hw : a' ≫ g.hom = f.hom ≫ b.hom := by
    rw [← h'.h₁, Category.assoc, hh, h.h₁]
  have hlocal : L.map a.hom = L.map a' :=
    (LeftHomotopyRel.factorsThroughLocalization C h'.leftHomotopyRel).map_eq L
  refine ⟨Arrow.homMk a' b.hom hw, ?_⟩
  ext
  · exact hlocal.symm.trans ha
  · exact hb

/-- The actual arrow comparison sends levelwise weak equivalences to isomorphisms. -/
theorem mapArrow_inverts :
    (weakEquivalences C).arrow.IsInvertedBy L.mapArrow := by
  intro f g φ hφ
  haveI : IsIso (L.map φ.left) := Localization.inverts L _ _ hφ.1
  haveI : IsIso (L.map φ.right) := Localization.inverts L _ _ hφ.2
  haveI : IsIso (L.mapArrow.map φ).left := by
    change IsIso (L.map φ.left)
    infer_instance
  haveI : IsIso (L.mapArrow.map φ).right := by
    change IsIso (L.map φ.right)
    infer_instance
  exact Arrow.isIso_of_isIso_left_of_isIso_right _

/-- The comparison from localized actual arrows to arrows of the localization. -/
public noncomputable def derivedArrowFunctor :
    (weakEquivalences C).arrow.Localization ⥤ Arrow H :=
  Localization.lift L.mapArrow (show (weakEquivalences C).arrow.IsInvertedBy L.mapArrow from by
    exact mapArrow_inverts L) (weakEquivalences C).arrow.Q

public noncomputable def derivedArrowComparison :
    (weakEquivalences C).arrow.Q ⋙ derivedArrowFunctor L ≅ L.mapArrow :=
  Localization.fac L.mapArrow (show (weakEquivalences C).arrow.IsInvertedBy L.mapArrow from by
    exact mapArrow_inverts L) (weakEquivalences C).arrow.Q

def goodArrows : ObjectProperty (Arrow C) := fun f =>
  IsCofibrant f.left ∧ IsFibrant f.left ∧
    IsCofibrant f.right ∧ IsFibrant f.right ∧ Fibration f.hom

/-- Every arrow is connected through levelwise weak equivalences to a
fibration between bifibrant objects. -/
lemma exists_goodArrow (f : Arrow C) :
    ∃ g : Arrow C, goodArrows g ∧
      Nonempty ((weakEquivalences C).arrow.Q.obj g ≅
        (weakEquivalences C).arrow.Q.obj f) := by
  let Q := (weakEquivalences C).arrow.Q
  let q : Arrow C := Arrow.mk (CofibrantObject.HoCat.resolutionMap f.hom)
  let p : q ⟶ f := Arrow.homMk
    (CofibrantObject.HoCat.pResolutionObj f.left)
    (CofibrantObject.HoCat.pResolutionObj f.right)
    (CofibrantObject.HoCat.resolutionMap_fac f.hom).symm
  haveI : IsCofibrant q.left := by
    change IsCofibrant (CofibrantObject.HoCat.resolutionObj f.left)
    infer_instance
  haveI : IsCofibrant q.right := by
    change IsCofibrant (CofibrantObject.HoCat.resolutionObj f.right)
    infer_instance
  let a : CofibrantObject C := CofibrantObject.mk q.left
  let b : CofibrantObject C := CofibrantObject.mk q.right
  let r := CofibrantObject.bifibrantResolutionMap
    (CofibrantObject.homMk q.hom : a ⟶ b)
  let rArrow : Arrow C := Arrow.mk r.hom
  let i : q ⟶ rArrow := Arrow.homMk
    (CofibrantObject.iBifibrantResolutionObj a).hom
    (CofibrantObject.iBifibrantResolutionObj b).hom
    (CofibrantObject.ι.congr_map (CofibrantObject.bifibrantResolutionMap_fac
      (CofibrantObject.homMk q.hom : a ⟶ b)))
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    r.hom
  haveI : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
  haveI : IsFibrant d.Z := isFibrant_of_fibration d.p
  let g : Arrow C := Arrow.mk d.p
  let j : rArrow ⟶ g := Arrow.homMk d.i (𝟙 _) (by simp [rArrow, g])
  haveI : IsIso (Q.map p) := Localization.inverts Q (weakEquivalences C).arrow p (by
    constructor <;> dsimp [p] <;> exact mem_weakEquivalences _)
  haveI : IsIso (Q.map i) := Localization.inverts Q (weakEquivalences C).arrow i (by
    constructor <;> dsimp [i] <;> exact mem_weakEquivalences _)
  haveI : IsIso (Q.map j) := Localization.inverts Q (weakEquivalences C).arrow j (by
    constructor <;> dsimp [j] <;> exact mem_weakEquivalences _)
  refine ⟨g, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨(asIso (Q.map j)).symm ≪≫ (asIso (Q.map i)).symm ≪≫ asIso (Q.map p)⟩⟩ <;>
    dsimp [g] <;> infer_instance

lemma goodArrows_localization_essSurj :
    (goodArrows.ι ⋙ (weakEquivalences C).arrow.Q).EssSurj := by
  let Q := (weakEquivalences C).arrow.Q
  letI := Localization.essSurj Q (weakEquivalences C).arrow
  refine ⟨fun X => ?_⟩
  obtain ⟨f, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Q X
  obtain ⟨g, hg, ⟨eg⟩⟩ := exists_goodArrow f
  exact ⟨⟨g, hg⟩, ⟨eg ≪≫ e⟩⟩

lemma goodArrows_mapArrow_full : (goodArrows.ι ⋙ L.mapArrow).Full := by
  constructor
  intro f g φ
  haveI := f.property.1
  haveI := f.property.2.1
  haveI := f.property.2.2.1
  haveI := f.property.2.2.2.1
  haveI := g.property.1
  haveI := g.property.2.1
  haveI := g.property.2.2.1
  haveI := g.property.2.2.2.1
  haveI := g.property.2.2.2.2
  obtain ⟨ψ, hψ⟩ := strictify_square L (f := f.obj) (g := g.obj) φ
  exact ⟨ObjectProperty.homMk ψ, hψ⟩

/-- Fullness of the comparison from localized point-set arrows
to arrows in the homotopy category. -/
public theorem derivedArrowFunctor_full : (derivedArrowFunctor L).Full := by
  let Q := (weakEquivalences C).arrow.Q
  let I := (goodArrows (C := C)).ι
  letI := goodArrows_localization_essSurj (C := C)
  letI := goodArrows_mapArrow_full L
  haveI : ((I ⋙ Q) ⋙ derivedArrowFunctor L).Full :=
    Functor.Full.of_iso (isoWhiskerLeft I (derivedArrowComparison L)).symm
  apply Functor.full_of_comp_essSurj (derivedArrowFunctor L) (I ⋙ Q)
  intro f g φ
  obtain ⟨ψ, hψ⟩ := ((I ⋙ Q) ⋙ derivedArrowFunctor L).map_surjective φ
  exact ⟨(I ⋙ Q).map ψ, hψ⟩

end KIP126.StableHomotopy.ModelFoundation
