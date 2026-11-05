module

public import KIP126.AdamsSynthetic.Context
public import KIP126.AdamsSynthetic.ModelFoundation.Pretriangulated
public import KIP126.AdamsSynthetic.ModelFoundation.DerivedMonoidal
public import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy

/-! Primitive point-set presentations of the specified target categories.
The target additive, shifted, tensor and pretriangulated structures are derived
from the same model and localization. Stability is equivalence of the actual
model-derived suspension. No target triangle or square-comparison conclusion
is a field of these primitive presentations. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomotopicalAlgebra
universe u v w z w' z'
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]
  {H' : Type w'} [Category.{z'} H'] (E : H ≌ H')

/-- The two actual derived suspensions agree under an equivalence of the
localization target. Both are lifts of the same point-set suspension. -/
private def derivedSuspensionCompEquivalenceIso :
    G.derivedSuspensionFunctor L ⋙ E.functor ≅
      E.functor ⋙ G.derivedSuspensionFunctor (L ⋙ E.functor) :=
  (Localization.fullyFaithfulWhiskeringLeft L (weakEquivalences C) H').preimageIso
    ((Functor.associator L (G.derivedSuspensionFunctor L) E.functor).symm ≪≫
      isoWhiskerRight (G.derivedSuspensionFunctorComparison L) E.functor ≪≫
      Functor.associator G.suspensionFunctor L E.functor ≪≫
      (G.derivedSuspensionFunctorComparison (L ⋙ E.functor)).symm ≪≫
      Functor.associator L E.functor (G.derivedSuspensionFunctor (L ⋙ E.functor)))

/-- The comparison intertwines the point-set suspension maps after localization. -/
private theorem derivedSuspensionCompEquivalenceIso_hom_app (X : C) :
    (G.derivedSuspensionCompEquivalenceIso L E).hom.app (L.obj X) ≫
      (G.derivedSuspensionFunctorComparison (L ⋙ E.functor)).hom.app X =
    E.functor.map ((G.derivedSuspensionFunctorComparison L).hom.app X) := by
  let e :=
    (Functor.associator L (G.derivedSuspensionFunctor L) E.functor).symm ≪≫
      isoWhiskerRight (G.derivedSuspensionFunctorComparison L) E.functor ≪≫
      Functor.associator G.suspensionFunctor L E.functor ≪≫
      (G.derivedSuspensionFunctorComparison (L ⋙ E.functor)).symm ≪≫
      Functor.associator L E.functor (G.derivedSuspensionFunctor (L ⋙ E.functor))
  have h := congrArg (fun τ => τ.app X)
    ((Localization.fullyFaithfulWhiskeringLeft L (weakEquivalences C) H').map_preimage e.hom)
  have h' : (G.derivedSuspensionCompEquivalenceIso L E).hom.app (L.obj X) =
      E.functor.map ((G.derivedSuspensionFunctorComparison L).hom.app X) ≫
        (G.derivedSuspensionFunctorComparison (L ⋙ E.functor)).inv.app X := by
    simpa [e, derivedSuspensionCompEquivalenceIso,
      Functor.FullyFaithful.preimageIso] using h
  rw [h']
  simp

/-- Stability of the actual model suspension is preserved when the localization
target is replaced by an equivalent category. -/
private theorem derivedSuspension_isEquivalence_compEquivalence
    [(G.derivedSuspensionFunctor L).IsEquivalence] :
    (G.derivedSuspensionFunctor (L ⋙ E.functor)).IsEquivalence := by
  haveI : (E.functor ⋙ G.derivedSuspensionFunctor (L ⋙ E.functor)).IsEquivalence :=
    Functor.isEquivalence_of_iso (G.derivedSuspensionCompEquivalenceIso L E)
  exact Functor.isEquivalence_of_comp_left E.functor _

end
end KIP126.StableHomotopy.CofibrantGeneration
end

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Pretriangulated
universe u v w z
noncomputable section

set_option linter.checkUnivs false in
/-- A pointed cofibrantly generated model localizing to the same specified category.
Its stability premise concerns the suspension actually constructed from this model. -/
public structure StableModelPresentation (H : Type w) [Category.{z} H] where
  PointSet : Type u
  pointSetCategory : Category.{v} PointSet
  pointSetModel : ModelCategory PointSet
  modelGeneration : CofibrantGeneration PointSet
  zeroMorphisms : HasZeroMorphisms PointSet
  zeroObject : HasZeroObject PointSet
  localization : PointSet ⥤ H
  localizes : localization.IsLocalization (weakEquivalences PointSet)
  actualStable :
    letI := localizes
    (modelGeneration.derivedSuspensionFunctor localization).IsEquivalence

set_option linter.checkUnivs false in
/-- A symmetric monoidal model presentation. Target tensor and triangle structure
are derived, including the monoidal unit comparison. -/
public structure SpectrumModelPresentation (H : Type w) [Category.{z} H]
    extends StableModelPresentation.{u,v,w,z} H where
  monoidal : MonoidalCategory PointSet
  symmetric : SymmetricCategory PointSet
  closed : MonoidalClosed PointSet
  limits : HasLimits.{v,u} PointSet
  colimits : HasColimits.{v,u} PointSet
  monoidalModel : MonoidalModelCompatibility PointSet

namespace StableModelPresentation
variable {C : Type w} [Category.{z} C]

/-- The actual weak-equivalence localization of the supplied point-set model. -/
public abbrev Ho (R : StableModelPresentation.{u,v,w,z} C) : Type u :=
  letI := R.pointSetCategory
  letI := R.pointSetModel
  (weakEquivalences R.PointSet).Localization

/-- The equivalence with the localization target induced by `localizes`. -/
public noncomputable def homotopyEquivalence (R : StableModelPresentation.{u,v,w,z} C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    (weakEquivalences R.PointSet).Localization ≌ C := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.localizes
  exact Localization.equivalenceFromModel R.localization (weakEquivalences R.PointSet)

/-- The canonical quotient followed by the comparison is the supplied
localization functor, up to its canonical natural isomorphism. -/
public noncomputable def localizationComparison
    (R : StableModelPresentation.{u,v,w,z} C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    (weakEquivalences R.PointSet).Q ⋙ R.homotopyEquivalence.functor ≅ R.localization := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.localizes
  exact Localization.qCompEquivalenceFromModelFunctorIso
    R.localization (weakEquivalences R.PointSet)

/-- The actual point-set cofiber functor of this realization. All
functoriality laws come from the small object and pushout constructions. -/
public noncomputable def pointSetCofiberFunctor
    (R : StableModelPresentation.{u,v,w,z} C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    Arrow R.PointSet ⥤ R.PointSet := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.zeroMorphisms
  letI := R.zeroObject
  exact R.modelGeneration.cofiberFunctor

/-- Compose the actual point-set cofiber functor with the same localization.
The source is still the point-set arrow category, retaining its squares. -/
public noncomputable def localizedCofiberFunctor
    (R : StableModelPresentation.{u,v,w,z} C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    Arrow R.PointSet ⥤ C := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  exact R.pointSetCofiberFunctor ⋙ R.localization

end StableModelPresentation

@[implicit_reducible]
public def SpectrumModelPresentation.stableCategory {H : Type w} [Category.{z} H]
    (R : SpectrumModelPresentation.{u,v,w,z} H) : StableHomotopyCategory.{w,z} H := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.zeroMorphisms
  letI := R.zeroObject
  letI := R.localizes
  letI := R.actualStable
  letI := R.monoidal
  letI := R.symmetric
  letI := R.closed
  exact {
    toCategory := inferInstance
    toPreadditive := R.modelGeneration.modelPreadditive R.localization
    toHasShift := R.modelGeneration.derivedSuspensionHasShift R.localization
    toMonoidalCategory := R.modelGeneration.derivedMonoidalCategory R.monoidalModel R.localization
    hasZeroObject := localization_hasZeroObject R.localization (weakEquivalences R.PointSet)
    shiftAdditive := R.modelGeneration.modelShiftAdditive R.localization
    pretriangulated := R.modelGeneration.modelPretriangulated R.localization }

public theorem SpectrumModelPresentation.sameCategory {H : Type w} [Category.{z} H]
    (R : SpectrumModelPresentation.{u,v,w,z} H) :
    R.stableCategory.toCategory = (inferInstance : Category.{z} H) := rfl

public def SpectrumModelPresentation.suspensionComparison {H : Type w} [Category.{z} H]
    (R : SpectrumModelPresentation.{u,v,w,z} H) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    letI := R.zeroMorphisms
    letI := R.zeroObject
    letI := R.localizes
    letI := R.stableCategory
    shiftFunctor H (1 : ℤ) ≅ R.modelGeneration.derivedSuspensionFunctor R.localization := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.zeroMorphisms
  letI := R.zeroObject
  letI := R.localizes
  letI := R.actualStable
  exact R.modelGeneration.derivedSuspensionShiftOneIso R.localization

public theorem SpectrumModelPresentation.distinguishedClass {H : Type w} [Category.{z} H]
    (R : SpectrumModelPresentation.{u,v,w,z} H) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    letI := R.zeroMorphisms
    letI := R.zeroObject
    letI := R.localizes
    letI := R.actualStable
    letI := R.stableCategory
    distTriang H =
      R.modelGeneration.modelCofiberTriangles R.localization := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.zeroMorphisms
  letI := R.zeroObject
  letI := R.localizes
  letI := R.actualStable
  exact R.modelGeneration.modelPretriangulated_distinguished R.localization

public def SpectrumModelPresentation.derivedUnitComparison {H : Type w} [Category.{z} H]
    (R : SpectrumModelPresentation.{u,v,w,z} H) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    letI := R.monoidal
    letI := R.stableCategory
    (𝟙_ H) ≅ R.localization.obj
      (R.modelGeneration.cofibrantReplacementFunctor.obj (𝟙_ R.PointSet)) := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.localizes
  letI := R.monoidal
  letI := R.symmetric
  letI := R.closed
  exact R.modelGeneration.derivedUnitComparison R.monoidalModel R.localization

/-- Compatibility access to the same generating data. -/
public abbrev SpectrumModelPresentation.generation
    {H : Type w} [Category.{z} H] (R : SpectrumModelPresentation.{u,v,w,z} H) :
    @CofibrantGeneration R.PointSet R.pointSetCategory R.pointSetModel := R.modelGeneration

namespace SpectrumModelPresentation
variable {H : Type w} [Category.{z} H] (R : SpectrumModelPresentation.{u,v,w,z} H)

/-- The specified point-set tensor computes the target tensor on cofibrant inputs. -/
public def tensorComparison :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    letI := R.monoidal
    letI := R.stableCategory
    ∀ X Y : R.PointSet, IsCofibrant X → IsCofibrant Y →
      (R.localization.obj (X ⊗ Y) ≅ R.localization.obj X ⊗ R.localization.obj Y) := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.localizes
  letI := R.monoidal
  letI := R.symmetric
  letI := R.closed
  exact R.modelGeneration.derivedTensorComparison R.monoidalModel R.localization

/-- Naturality of the same derived tensor comparison. -/
public theorem tensorNaturality :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    letI := R.monoidal
    letI := R.stableCategory
    ∀ {X X' Y Y' : R.PointSet} (f : X ⟶ X') (g : Y ⟶ Y')
      (hX : IsCofibrant X) (hX' : IsCofibrant X')
      (hY : IsCofibrant Y) (hY' : IsCofibrant Y'),
    R.localization.map (f ⊗ₘ g) ≫ (R.tensorComparison X' Y' hX' hY').hom =
      (R.tensorComparison X Y hX hY).hom ≫ (R.localization.map f ⊗ₘ R.localization.map g) := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.localizes
  letI := R.monoidal
  letI := R.symmetric
  letI := R.closed
  intro X X' Y Y' f g hX hX' hY hY'
  exact R.modelGeneration.derivedTensorComparison_naturality R.monoidalModel R.localization
    f g hX hX' hY hY'

/-- Every weak equivalence to the point-set unit computes the same target sphere. -/
public def unitComparison :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    letI := R.monoidal
    letI := R.stableCategory
    ∀ {QI : R.PointSet} (q : QI ⟶ 𝟙_ R.PointSet),
      IsCofibrant QI → weakEquivalences R.PointSet q →
      (R.localization.obj QI ≅ SphereSpectrum (C := H)) := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.localizes
  letI := R.monoidal
  letI := R.symmetric
  letI := R.closed
  intro QI q _ hq
  exact R.modelGeneration.derivedUnitComparisonOfWeakEquivalence R.monoidalModel R.localization q hq

end SpectrumModelPresentation

/-- A model localization has Hom types no larger than those of its point-set model. -/
public theorem StableModelPresentation.locallySmall {H : Type w} [Category.{z} H]
    (R : StableModelPresentation.{u,v,w,z} H) : LocallySmall.{v} H := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.localizes
  exact HomotopicalAlgebra.locallySmall_of_isLocalization R.localization

/-- The canonical equivalence to the same objects with small Hom types.
Both object functions are identity. -/
public def SpectrumModelPresentation.smallHomEquivalence {H : Type w} [Category.{z} H]
    (R : SpectrumModelPresentation.{u,v,w,z} H) :
    letI := R.toStableModelPresentation.locallySmall
    H ≌ ShrinkHoms H := by
  letI := R.toStableModelPresentation.locallySmall
  exact ShrinkHoms.equivalence H

open CofibrantGeneration in
/-- Compose the same model localization with the canonical small-Hom equivalence.
Stability is transported by the comparison of the actual derived suspensions. -/
@[implicit_reducible]
public def SpectrumModelPresentation.shrinkHoms {H : Type w} [Category.{z} H]
    (R : SpectrumModelPresentation.{u,v,w,z} H) :
    letI := R.toStableModelPresentation.locallySmall
    SpectrumModelPresentation.{u,v,w,v} (ShrinkHoms H) := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.zeroMorphisms
  letI := R.zeroObject
  letI := R.localizes
  letI := R.actualStable
  letI := R.toStableModelPresentation.locallySmall
  exact {
    PointSet := R.PointSet
    pointSetCategory := R.pointSetCategory
    pointSetModel := R.pointSetModel
    modelGeneration := R.modelGeneration
    zeroMorphisms := R.zeroMorphisms
    zeroObject := R.zeroObject
    localization := R.localization ⋙ R.smallHomEquivalence.functor
    localizes := inferInstance
    actualStable := by
      exact derivedSuspension_isEquivalence_compEquivalence
        R.modelGeneration R.localization R.smallHomEquivalence
    monoidal := R.monoidal
    symmetric := R.symmetric
    closed := R.closed
    limits := R.limits
    colimits := R.colimits
    monoidalModel := R.monoidalModel }

/-- The small-Hom equivalence keeps each source object literally fixed. -/
public theorem SpectrumModelPresentation.smallHomEquivalence_obj
    {H : Type w} [Category.{z} H] (R : SpectrumModelPresentation.{u,v,w,z} H) (X : H) :
    letI := R.toStableModelPresentation.locallySmall
    R.smallHomEquivalence.functor.obj X = ShrinkHoms.toShrinkHoms X := rfl

set_option linter.checkUnivs false in
/-- The synthetic source category and its monoidal stable model,
with the specified grading and deformation data. -/
public structure SyntheticModelPresentation (Syn : Type w) where
  category : Category.{z} Syn
  model : SpectrumModelPresentation.{u,v,w,z} Syn
  biShift : ℤ × ℤ → Syn ⥤ Syn
  biShift_comp : ∀ a b, biShift a ⋙ biShift b ≅ biShift (a + b)
  biShift_zero : biShift (0, 0) ≅ 𝟭 Syn
  biShift_compat : letI := model.stableCategory
    ∀ n : ℤ, biShift (n, 0) ≅ shiftFunctor Syn n
  biShift_fullyFaithful : ∀ p, (biShift p).FullyFaithful
  lam : biShift (0, -1) ⟶ 𝟭 Syn
  biShift_tensor_comm : letI := model.stableCategory
    ∀ (p : ℤ × ℤ) (X Y : Syn),
      (biShift p).obj (MonoidalCategory.tensorObj X Y) ≅
        MonoidalCategory.tensorObj ((biShift p).obj X) Y

namespace SyntheticModelPresentation
variable {Syn : Type w} (R : SyntheticModelPresentation.{u,v,w,z} Syn)

/-- Assemble the derived stable category and the same additional synthetic data. -/
@[implicit_reducible]
public def syntheticCategory : KIP126.Synthetic.Context.SyntheticCategory.{w,z} Syn := by
  letI := R.category
  letI := R.model.stableCategory
  exact {
    toStableHomotopyCategory := R.model.stableCategory
    biShift := R.biShift
    biShift_comp := R.biShift_comp
    biShift_zero := R.biShift_zero
    biShift_compat := R.biShift_compat
    biShift_fullyFaithful := R.biShift_fullyFaithful
    lam := R.lam
    biShift_tensor_comm := R.biShift_tensor_comm }

/-- The assembled category is exactly the specified source category. -/
public theorem sameCategory :
    R.syntheticCategory.toStableHomotopyCategory.toCategory = R.category := rfl

/-- The underlying primitive stable-model presentation. -/
public abbrev toStableModelPresentation :
    @StableModelPresentation.{u,v,w,z} Syn R.category := by
  letI := R.category
  exact R.model.toStableModelPresentation

public abbrev PointSet : Type u := by
  letI := R.category
  exact R.model.PointSet
public abbrev pointSetCategory : Category.{v} R.PointSet := by
  letI := R.category
  exact R.model.pointSetCategory
public abbrev pointSetModel : @ModelCategory R.PointSet R.pointSetCategory := by
  letI := R.category
  exact R.model.pointSetModel
public abbrev modelGeneration : @CofibrantGeneration R.PointSet R.pointSetCategory R.pointSetModel :=
  by
    letI := R.category
    exact R.model.modelGeneration

/-- The same primitive localization, landing in the assembled source category. -/
public abbrev localization :
    letI := R.pointSetCategory
    letI := R.category
    R.PointSet ⥤ Syn := by
  letI := R.category
  exact R.model.localization

end SyntheticModelPresentation
end
end KIP126.StableHomotopy
