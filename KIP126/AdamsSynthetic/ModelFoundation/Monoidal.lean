module
public import KIP126.AdamsSynthetic.ModelFoundation.MonoidalCompatibility
public import KIP126.AdamsSynthetic.ModelFoundation.Generation
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-! Derived monoidal structures on cofibrant objects and objects isomorphic to the
point-set unit. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.ModelGoodMonoidal
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomotopicalAlgebra MonoidalCategory MorphismProperty
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  (M : MonoidalModelCompatibility C)

omit [SymmetricCategory C] in
include M in
private theorem whiskerRight_cofibration {A B : C} (f : A ⟶ B) (X : C)
    [Cofibration f] [IsCofibrant X] : Cofibration (f ▷ X) := by
  haveI : IsIso (f ▷ (⊥_ C)) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (tensorLeft A) (⊥_ C))
      (initialIsInitial.isInitialObj (tensorLeft B) (⊥_ C)) _
  rw [cofibration_iff]
  rw [show f ▷ X = pushout.inr (f ▷ (⊥_ C)) (A ◁ (initial.to X)) ≫
      (MonoidalCategory.Arrow.pushoutProduct.obj (Arrow.mk f) |>.obj
        (Arrow.mk (initial.to X))).hom from by
    have h := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f (initial.to X)).inr_ι
    simp only [curriedTensor_map_app, Functor.PushoutObjObj.ofHasPushout_inr] at h
    exact h.symm]
  exact (cofibrations C).comp_mem _ _ (mem_cofibrations _)
    (M.pushoutProduct f (initial.to X) (mem_cofibrations f) (mem_cofibrations _))

omit [SymmetricCategory C] in
include M in
private theorem whiskerRight_trivialCofibration {A B : C} (f : A ⟶ B) (X : C)
    [Cofibration f] [WeakEquivalence f] [IsCofibrant X] :
    trivialCofibrations C (f ▷ X) := by
  haveI : IsIso (f ▷ (⊥_ C)) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (tensorLeft A) (⊥_ C))
      (initialIsInitial.isInitialObj (tensorLeft B) (⊥_ C)) _
  rw [show f ▷ X = pushout.inr (f ▷ (⊥_ C)) (A ◁ (initial.to X)) ≫
      (MonoidalCategory.Arrow.pushoutProduct.obj (Arrow.mk f) |>.obj
        (Arrow.mk (initial.to X))).hom from by
    have h := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f (initial.to X)).inr_ι
    simp only [curriedTensor_map_app, Functor.PushoutObjObj.ofHasPushout_inr] at h
    exact h.symm]
  have hpp := M.pushoutProductTrivialLeft f (initial.to X)
    (mem_trivialCofibrations (f := f)) (mem_cofibrations _)
  exact ⟨(cofibrations C).comp_mem _ _ (mem_cofibrations _) hpp.1,
    (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences _) hpp.2⟩

omit [SymmetricCategory C] in
include M in
private theorem whiskerRight_weakEquivalence {A B : C} (f : A ⟶ B) (X : C)
    [WeakEquivalence f] [IsCofibrant A] [IsCofibrant B] [IsCofibrant X] :
    WeakEquivalence (f ▷ X) := by
  let F : CofibrantBrownFactorization f := Classical.choice inferInstance
  haveI : WeakEquivalence (F.i ▷ X) :=
    (weakEquivalence_iff _).2 (whiskerRight_trivialCofibration M F.i X).2
  haveI : WeakEquivalence (F.s ▷ X) :=
    (weakEquivalence_iff _).2 (whiskerRight_trivialCofibration M F.s X).2
  have hsection : F.s ▷ X ≫ F.p ▷ X = 𝟙 (B ⊗ X) := by
    rw [← comp_whiskerRight, F.s_p, id_whiskerRight]
  haveI : WeakEquivalence (F.p ▷ X) := weakEquivalence_of_precomp_of_fac hsection
  rw [show f ▷ X = F.i ▷ X ≫ F.p ▷ X by rw [← comp_whiskerRight, F.fac]]
  infer_instance

include M in
private theorem tensor_isCofibrant (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    IsCofibrant (X ⊗ Y) := by
  have hsource : IsInitial ((⊥_ C) ⊗ Y) :=
    (initialIsInitial.isInitialObj (tensorLeft Y) (⊥_ C)).ofIso (β_ Y (⊥_ C))
  exact (isCofibrant_iff_of_isInitial ((initial.to X) ▷ Y) hsource).2
    (whiskerRight_cofibration M (initial.to X) Y)

private def goodObjects (C : Type u) [Category.{v} C] [ModelCategory C]
    [MonoidalCategory C] : ObjectProperty C :=
  fun X => IsCofibrant X ∨ Nonempty (X ≅ 𝟙_ C)

include M in
private abbrev goodObjectsMonoidal : (goodObjects C).IsMonoidal where
  prop_unit := Or.inr ⟨Iso.refl _⟩
  prop_tensor X Y hX hY := by
    rcases hX with hX | eX <;> rcases hY with hY | eY
    · letI := hX
      letI := hY
      exact Or.inl (tensor_isCofibrant M X Y)
    · letI := hX
      let eY := Classical.choice eY
      let e : X ⊗ Y ≅ X := (Iso.refl X ⊗ᵢ eY) ≪≫ ρ_ X
      exact Or.inl (isCofibrant_of_cofibration e.inv)
    · letI := hY
      let eX := Classical.choice eX
      let e : X ⊗ Y ≅ Y := (eX ⊗ᵢ Iso.refl Y) ≪≫ λ_ Y
      exact Or.inl (isCofibrant_of_cofibration e.inv)
    · exact Or.inr ⟨(Classical.choice eX ⊗ᵢ Classical.choice eY) ≪≫ λ_ (𝟙_ C)⟩

omit [SymmetricCategory C] [MonoidalClosed C] in
private theorem whiskerRight_weakEquivalence_isoUnit {A B X : C} (f : A ⟶ B)
    [WeakEquivalence f] (e : X ≅ 𝟙_ C) : WeakEquivalence (f ▷ X) := by
  haveI : WeakEquivalence (f ▷ (𝟙_ C)) := by
    haveI : WeakEquivalence ((ρ_ A).hom ≫ f) := inferInstance
    exact weakEquivalence_of_postcomp_of_fac (rightUnitor_naturality f)
  haveI : WeakEquivalence ((A ◁ e.hom) ≫ (f ▷ (𝟙_ C))) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac (whisker_exchange f e.hom).symm

variable (G : CofibrantGeneration C)

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] in
private theorem replacement_map_weakEquivalence {A B : C} (f : A ⟶ B)
    [WeakEquivalence f] : WeakEquivalence (G.cofibrantReplacementFunctor.map f) := by
  haveI : WeakEquivalence (G.cofibrantReplacementCounit.app A) :=
    (weakEquivalence_iff _).2 (G.cofibrantReplacementCounit_weakEquivalence A)
  haveI : WeakEquivalence (G.cofibrantReplacementCounit.app B) :=
    (weakEquivalence_iff _).2 (G.cofibrantReplacementCounit_weakEquivalence B)
  haveI : WeakEquivalence (G.cofibrantReplacementCounit.app A ≫ f) := inferInstance
  have h := G.cofibrantReplacementCounit.naturality f
  change G.cofibrantReplacementFunctor.map f ≫ G.cofibrantReplacementCounit.app B =
    G.cofibrantReplacementCounit.app A ≫ f at h
  exact weakEquivalence_of_postcomp_of_fac h

omit [SymmetricCategory C] in
include M in
private theorem replacementCounit_whiskerRight_cofibrant (X Y : C)
    (hX : goodObjects C X) [IsCofibrant Y] :
    WeakEquivalence (G.cofibrantReplacementCounit.app X ▷ Y) := by
  letI := G.cofibrantReplacement_isCofibrant X
  haveI : WeakEquivalence (G.cofibrantReplacementCounit.app X) :=
    (weakEquivalence_iff _).2 (G.cofibrantReplacementCounit_weakEquivalence X)
  rcases hX with hX | eX
  · letI := hX
    exact whiskerRight_weakEquivalence M (A := G.cofibrantReplacementFunctor.obj X)
      (B := X) (G.cofibrantReplacementCounit.app X) Y
  · let eX := Classical.choice eX
    haveI : WeakEquivalence
        ((G.cofibrantReplacementCounit.app X ≫ eX.hom) ▷ Y) :=
      (weakEquivalence_iff _).2 (M.unit
        (G.cofibrantReplacementCounit.app X ≫ eX.hom)
        (G.cofibrantReplacement_isCofibrant X) (mem_weakEquivalences _) Y inferInstance)
    have h : G.cofibrantReplacementCounit.app X ▷ Y ≫ eX.hom ▷ Y =
        (G.cofibrantReplacementCounit.app X ≫ eX.hom) ▷ Y :=
      (comp_whiskerRight _ _ _).symm
    exact weakEquivalence_of_postcomp_of_fac h

omit [SymmetricCategory C] in
include M G in
private theorem whiskerRight_weakEquivalence_good {A B : C} (f : A ⟶ B)
    [WeakEquivalence f] (hA : goodObjects C A) (hB : goodObjects C B)
    (X : C) (hX : goodObjects C X) : WeakEquivalence (f ▷ X) := by
  rcases hX with hX | eX
  · letI := hX
    letI := G.cofibrantReplacement_isCofibrant A
    letI := G.cofibrantReplacement_isCofibrant B
    letI := replacement_map_weakEquivalence G f
    letI := whiskerRight_weakEquivalence M (G.cofibrantReplacementFunctor.map f) X
    letI := replacementCounit_whiskerRight_cofibrant M G A X hA
    letI := replacementCounit_whiskerRight_cofibrant M G B X hB
    have h := congrArg (fun k => k ▷ X) (G.cofibrantReplacementCounit.naturality f)
    rw [comp_whiskerRight, comp_whiskerRight] at h
    haveI : WeakEquivalence ((G.cofibrantReplacementFunctor.map f ▷ X) ≫
        (G.cofibrantReplacementCounit.app B ▷ X)) := inferInstance
    exact weakEquivalence_of_precomp_of_fac h.symm
  · exact whiskerRight_weakEquivalence_isoUnit f (Classical.choice eX)

include M G in
private theorem whiskerLeft_weakEquivalence_good {A B : C} (f : A ⟶ B)
    [WeakEquivalence f] (hA : goodObjects C A) (hB : goodObjects C B)
    (X : C) (hX : goodObjects C X) : WeakEquivalence (X ◁ f) := by
  letI := whiskerRight_weakEquivalence_good M G f hA hB X hX
  haveI : WeakEquivalence ((β_ X A).hom ≫ (f ▷ X)) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac (BraidedCategory.braiding_naturality_right X f)

private def goodWeakEquivalences : MorphismProperty (goodObjects C).FullSubcategory :=
  (weakEquivalences C).inverseImage (goodObjects C).ι

include M G in
private theorem goodWeakEquivalences_isMonoidal :
    letI := goodObjectsMonoidal M
    (goodWeakEquivalences (C := C)).IsMonoidal := by
  letI := goodObjectsMonoidal M
  refine { toIsMultiplicative := ?_, whiskerLeft := ?_, whiskerRight := ?_ }
  · dsimp [goodWeakEquivalences]
    infer_instance
  · intro X Y₁ Y₂ g hg
    change weakEquivalences C (X.obj ◁ g.hom)
    haveI : WeakEquivalence g.hom := (weakEquivalence_iff _).2 hg
    exact (weakEquivalence_iff _).1
      (whiskerLeft_weakEquivalence_good M G g.hom Y₁.property Y₂.property X.obj X.property)
  · intro X₁ X₂ f hf Y
    change weakEquivalences C (f.hom ▷ Y.obj)
    haveI : WeakEquivalence f.hom := (weakEquivalence_iff _).2 hf
    exact (weakEquivalence_iff _).1
      (whiskerRight_weakEquivalence_good M G f.hom X₁.property X₂.property Y.obj Y.property)

include M in
private theorem replacementCounit_tensor_good (X Y : C)
    (hX : goodObjects C X) (hY : goodObjects C Y) :
    weakEquivalences C (G.cofibrantReplacementCounit.app X ⊗ₘ
      G.cofibrantReplacementCounit.app Y) := by
  let qX : G.cofibrantReplacementFunctor.obj X ⟶ X :=
    G.cofibrantReplacementCounit.app X
  let qY : G.cofibrantReplacementFunctor.obj Y ⟶ Y :=
    G.cofibrantReplacementCounit.app Y
  haveI : WeakEquivalence qX :=
    (weakEquivalence_iff _).2 (G.cofibrantReplacementCounit_weakEquivalence X)
  haveI : WeakEquivalence qY :=
    (weakEquivalence_iff _).2 (G.cofibrantReplacementCounit_weakEquivalence Y)
  let hQX : goodObjects C (G.cofibrantReplacementFunctor.obj X) :=
    Or.inl (G.cofibrantReplacement_isCofibrant X)
  let hQY : goodObjects C (G.cofibrantReplacementFunctor.obj Y) :=
    Or.inl (G.cofibrantReplacement_isCofibrant Y)
  haveI : WeakEquivalence (qX ▷ G.cofibrantReplacementFunctor.obj Y) :=
    whiskerRight_weakEquivalence_good M G qX hQX hX _ hQY
  haveI : WeakEquivalence (X ◁ qY) :=
    whiskerLeft_weakEquivalence_good M G qY hQY hY X hX
  change weakEquivalences C (qX ⊗ₘ qY)
  rw [tensorHom_def]
  exact mem_weakEquivalences _



end KIP126.StableHomotopy.ModelGoodMonoidal
