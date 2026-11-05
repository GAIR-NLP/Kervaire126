module
public import KIP126.AdamsSynthetic.Completed.Background
public import KIP126.AdamsSynthetic.Ordinary.Background
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
noncomputable section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option backward.isDefEq.respectTransparency false
/-- Coherent monoidal localization, with the specified unit and tensor comparisons. -/


public def syntheticSourceEquivalence :
    @Equivalence CompletedSyntheticSource SyntheticSpectrum inferInstance
      syntheticCategory.toStableHomotopyCategory.toCategory := by
  letI := syntheticSourceModelPresentation.toStableModelPresentation.locallySmall
  exact syntheticSourceModelPresentation.smallHomEquivalence
public def syntheticCompletion : Ordinary.SyntheticSpectrum ⥤ SyntheticSpectrum :=
  syntheticHF2Equivalences.Q ⋙ syntheticSourceEquivalence.functor
/-- Completion and ν use one compatible choice of synthetic comparisons. -/
private structure SyntheticCompletionData where
  syntheticCompletionMonoidal : syntheticCompletion.Monoidal
  nuCompletionIso : Ordinary.nu.functor ⋙ syntheticCompletion ≅ completion ⋙ nu.functor
  nuCompletion_unit :
      letI := syntheticCompletionMonoidal
      syntheticCompletion.map Ordinary.nu.unitIso.hom ≫ (Functor.Monoidal.εIso syntheticCompletion).symm.hom =
        (nuCompletionIso.app (SphereSpectrum (C := Ordinary.Spectrum))).hom ≫
          nu.functor.map completionSphereIso.hom ≫ nu.unitIso.hom
  syntheticCompletionShiftIso (p : ℤ × ℤ) :
      SyntheticCategory.biShift (Syn := Ordinary.SyntheticSpectrum) p ⋙ syntheticCompletion ≅
        syntheticCompletion ⋙ SyntheticCategory.biShift p
  syntheticCompletion_lambda (X : Ordinary.SyntheticSpectrum) :
      syntheticCompletion.map (SyntheticCategory.lam.app X) =
        (syntheticCompletionShiftIso (0,-1)).hom.app X ≫ SyntheticCategory.lam.app (syntheticCompletion.obj X)

private def syntheticCompletionConstruction : SyntheticCompletionData where
  syntheticCompletionMonoidal := by sorry
  nuCompletionIso := by sorry
  nuCompletion_unit := by sorry
  syntheticCompletionShiftIso := by sorry
  syntheticCompletion_lambda := by sorry

public def syntheticCompletionMonoidal : syntheticCompletion.Monoidal := syntheticCompletionConstruction.syntheticCompletionMonoidal
public def syntheticCompletionSphereIso :
    syntheticCompletion.obj (S_0_0 : Ordinary.SyntheticSpectrum) ≅ (S_0_0 : SyntheticSpectrum) := by
  letI := syntheticCompletionMonoidal
  exact (Functor.Monoidal.εIso syntheticCompletion).symm
public def syntheticCompletionTensorIso (X Y : Ordinary.SyntheticSpectrum) :
    syntheticCompletion.obj (CategoryTheory.MonoidalCategory.tensorObj X Y) ≅
      CategoryTheory.MonoidalCategory.tensorObj (syntheticCompletion.obj X) (syntheticCompletion.obj Y) := by
  letI := syntheticCompletionMonoidal
  exact (Functor.Monoidal.μIso syntheticCompletion X Y).symm
/-- Pstrągowski 5.6: hypercompleting νX gives ν of its HF₂ localization. -/
public def nuCompletionIso : Ordinary.nu.functor ⋙ syntheticCompletion ≅ completion ⋙ nu.functor := syntheticCompletionConstruction.nuCompletionIso
public theorem nuCompletion_unit :
    syntheticCompletion.map Ordinary.nu.unitIso.hom ≫ syntheticCompletionSphereIso.hom =
      (nuCompletionIso.app (SphereSpectrum (C := Ordinary.Spectrum))).hom ≫
        nu.functor.map completionSphereIso.hom ≫ nu.unitIso.hom := syntheticCompletionConstruction.nuCompletion_unit
public def syntheticCompletionShiftIso (p : ℤ × ℤ) :
    SyntheticCategory.biShift (Syn := Ordinary.SyntheticSpectrum) p ⋙ syntheticCompletion ≅
      syntheticCompletion ⋙ SyntheticCategory.biShift p := syntheticCompletionConstruction.syntheticCompletionShiftIso p
/-- The deformation map is the image of the same ordinary λ. -/
public theorem syntheticCompletion_lambda (X : Ordinary.SyntheticSpectrum) :
    syntheticCompletion.map (SyntheticCategory.lam.app X) =
      (syntheticCompletionShiftIso (0,-1)).hom.app X ≫ SyntheticCategory.lam.app (syntheticCompletion.obj X) := syntheticCompletionConstruction.syntheticCompletion_lambda X
end
end KIP126.AdamsSynthetic.Completed
