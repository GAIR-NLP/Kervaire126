module
import all KIP126.AdamsSynthetic.ModelFoundation.Monoidal
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.ModelGoodMonoidal
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor
open HomotopicalAlgebra MonoidalCategory MorphismProperty Localization
universe u v w z
noncomputable section

private theorem localizedEquivalence_of_counits
    {A B : Type*} [Category* A] [Category* B]
    {WA : MorphismProperty A} {WB : MorphismProperty B}
    (F : LocalizerMorphism WA WB) (R : LocalizerMorphism WB WA)
    (εA : F.functor ⋙ R.functor ⟶ 𝟭 A) (εB : R.functor ⋙ F.functor ⟶ 𝟭 B)
    (hA : ∀ X, WA (εA.app X)) (hB : ∀ X, WB (εB.app X)) :
    F.IsLocalizedEquivalence := by
  have : IsIso (whiskerRight εA WA.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun _ => Localization.inverts WA.Q WA _ (hA _)
  have : IsIso (whiskerRight εB WB.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun _ => Localization.inverts WB.Q WB _ (hB _)
  refine ⟨(Localization.equivalence WA.Q WA WB.Q WB (F.functor ⋙ WB.Q)
    (F.localizedFunctor WA.Q WB.Q)
    (R.functor ⋙ WA.Q) (R.localizedFunctor WB.Q WA.Q) ?_ ?_).isEquivalence_functor⟩
  · exact Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (CatCommSq.iso R.functor WB.Q WA.Q _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      asIso (whiskerRight εA WA.Q) ≪≫ Functor.leftUnitor _
  · exact Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (CatCommSq.iso F.functor WA.Q WB.Q _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      asIso (whiskerRight εB WB.Q) ≪≫ Functor.leftUnitor _

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  (G : CofibrantGeneration C)

private def goodReplacementFunctor : C ⥤ (goodObjects C).FullSubcategory :=
  (goodObjects C).lift G.cofibrantReplacementFunctor
    (fun X => Or.inl (G.cofibrantReplacement_isCofibrant X))

private def goodInclusionLocalizer :
    LocalizerMorphism (goodWeakEquivalences (C := C)) (weakEquivalences C) :=
  LocalizerMorphism.ofEq rfl

private def goodReplacementLocalizer :
    LocalizerMorphism (weakEquivalences C) (goodWeakEquivalences (C := C)) where
  functor := goodReplacementFunctor G
  map X Y f hf := by
    change weakEquivalences C (G.cofibrantReplacementFunctor.map f)
    haveI : WeakEquivalence f := (weakEquivalence_iff _).2 hf
    exact (weakEquivalence_iff _).1 (replacement_map_weakEquivalence G f)

private def goodReplacementCounit :
    (goodObjects C).ι ⋙ goodReplacementFunctor G ⟶ 𝟭 (goodObjects C).FullSubcategory where
  app X := ObjectProperty.homMk (G.cofibrantReplacementCounit.app X.obj)
  naturality X Y f := by
    ext
    exact G.cofibrantReplacementCounit.naturality f.hom

include G in
private theorem goodInclusion_isLocalizedEquivalence :
    (goodInclusionLocalizer (C := C)).IsLocalizedEquivalence := by
  exact localizedEquivalence_of_counits (goodInclusionLocalizer (C := C))
    (goodReplacementLocalizer G) (goodReplacementCounit G) G.cofibrantReplacementCounit
    (fun X => G.cofibrantReplacementCounit_weakEquivalence X.obj)
    G.cofibrantReplacementCounit_weakEquivalence

include G in
private theorem goodInclusion_isLocalization
    {H : Type w} [Category.{z} H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] :
    ((goodObjects C).ι ⋙ L).IsLocalization (goodWeakEquivalences (C := C)) := by
  letI := goodInclusion_isLocalizedEquivalence G
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (goodInclusionLocalizer (C := C)) L

end
end KIP126.StableHomotopy.ModelGoodMonoidal
