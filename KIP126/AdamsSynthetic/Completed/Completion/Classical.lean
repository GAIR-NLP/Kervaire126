module

public import KIP126.AdamsSynthetic.Completed.Coefficients
public import KIP126.AdamsSynthetic.Ordinary.Background

/-! One completion functor, its local-object reflection, and its specified
structural comparisons. Sphere and tensor comparisons are derived from the
same monoidal structure. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory MonoidalCategory KIP126.StableHomotopy KIP126.Synthetic.Context
noncomputable section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option backward.isDefEq.respectTransparency false

public def IsHF2Local (X : Ordinary.Spectrum) : Prop :=
  ∀ ⦃A B : ClassicalSource⦄ (f : A ⟶ B), classicalHF2Equivalences Ordinary.sourceComparison f →
    Function.Bijective (fun a : Ordinary.sourceComparison.equivalence.functor.obj B ⟶ X =>
      Ordinary.sourceComparison.equivalence.functor.map f ≫ a)

private structure ClassicalCompletionData where
  completionMonoidal : completion.Monoidal
  completedInclusion : Spectrum ⥤ Ordinary.Spectrum
  completedInclusionFullyFaithful : completedInclusion.FullyFaithful
  completionAdjunction : completion ⊣ completedInclusion
  completedInclusion_local (X : Spectrum) : IsHF2Local (completedInclusion.obj X)
  localObjectIso (X : Ordinary.Spectrum) (hX : IsHF2Local X) :
      completedInclusion.obj (completion.obj X) ≅ X
  completionShiftIso (n : ℤ) :
      shiftFunctor Ordinary.Spectrum n ⋙ completion ≅ completion ⋙ shiftFunctor Spectrum n
  completionCoefficientIso :
      completion.obj Ordinary.coefficients.object ≅ coefficients.object
  completion_coefficient_unit :
      letI := completionMonoidal
      completion.map Ordinary.coefficients.unit ≫ completionCoefficientIso.hom =
        (Functor.Monoidal.εIso completion).symm.hom ≫ coefficients.unit
  completionCofiberIso {X Y : Ordinary.Spectrum} (f : X ⟶ Y) :
      completion.obj (HasFunctorialCofiber.cofib f) ≅ HasFunctorialCofiber.cofib (completion.map f)
  completion_cofiber_inclusion {X Y : Ordinary.Spectrum} (f : X ⟶ Y) :
      completion.map (HasFunctorialCofiber.cofibι f) ≫ (completionCofiberIso f).hom =
        HasFunctorialCofiber.cofibι (completion.map f)
  completion_cofiber_boundary {X Y : Ordinary.Spectrum} (f : X ⟶ Y) :
      completion.map (HasFunctorialCofiber.cofibδ f) ≫ (completionShiftIso 1).hom.app X =
        (completionCofiberIso f).hom ≫ HasFunctorialCofiber.cofibδ (completion.map f)

private def classicalCompletionConstruction : ClassicalCompletionData where
  completionMonoidal := by sorry
  completedInclusion := by sorry
  completedInclusionFullyFaithful := by sorry
  completionAdjunction := by sorry
  completedInclusion_local := by sorry
  localObjectIso := by sorry
  completionShiftIso := by sorry
  completionCoefficientIso := by sorry
  completion_coefficient_unit := by sorry
  completionCofiberIso := by sorry
  completion_cofiber_inclusion := by sorry
  completion_cofiber_boundary := by sorry

public def completionMonoidal : completion.Monoidal :=
  classicalCompletionConstruction.completionMonoidal

public def completionSphereIso :
    completion.obj (SphereSpectrum (C := Ordinary.Spectrum)) ≅ (SphereSpectrum : Spectrum) := by
  letI := completionMonoidal
  exact (Functor.Monoidal.εIso completion).symm

public def completionTensorIso (X Y : Ordinary.Spectrum) :
    completion.obj (X ⊗ Y) ≅ completion.obj X ⊗ completion.obj Y := by
  letI := completionMonoidal
  exact (Functor.Monoidal.μIso completion X Y).symm

public theorem completionMonoidal_unit :
    letI := completionMonoidal
    (Functor.Monoidal.εIso completion).symm = completionSphereIso := rfl

public theorem completionMonoidal_tensor (X Y : Ordinary.Spectrum) :
    letI := completionMonoidal
    (Functor.Monoidal.μIso completion X Y).symm = completionTensorIso X Y := rfl

public def completedInclusion : Spectrum ⥤ Ordinary.Spectrum := classicalCompletionConstruction.completedInclusion

public def completedInclusionFullyFaithful : completedInclusion.FullyFaithful := classicalCompletionConstruction.completedInclusionFullyFaithful

public def completionAdjunction : completion ⊣ completedInclusion := classicalCompletionConstruction.completionAdjunction

public theorem completedInclusion_local (X : Spectrum) : IsHF2Local (completedInclusion.obj X) := classicalCompletionConstruction.completedInclusion_local X

public def localObjectIso (X : Ordinary.Spectrum) (hX : IsHF2Local X) :
    completedInclusion.obj (completion.obj X) ≅ X := classicalCompletionConstruction.localObjectIso X hX

public def completionShiftIso (n : ℤ) :
    shiftFunctor Ordinary.Spectrum n ⋙ completion ≅ completion ⋙ shiftFunctor Spectrum n := classicalCompletionConstruction.completionShiftIso n

public def completionCoefficientIso :
    completion.obj Ordinary.coefficients.object ≅ coefficients.object := classicalCompletionConstruction.completionCoefficientIso

public theorem completion_coefficient_unit :
    completion.map Ordinary.coefficients.unit ≫ completionCoefficientIso.hom =
      completionSphereIso.hom ≫ coefficients.unit := classicalCompletionConstruction.completion_coefficient_unit

public def completionCofiberIso {X Y : Ordinary.Spectrum} (f : X ⟶ Y) :
    completion.obj (HasFunctorialCofiber.cofib f) ≅ HasFunctorialCofiber.cofib (completion.map f) := classicalCompletionConstruction.completionCofiberIso f

public theorem completion_cofiber_inclusion {X Y : Ordinary.Spectrum} (f : X ⟶ Y) :
    completion.map (HasFunctorialCofiber.cofibι f) ≫ (completionCofiberIso f).hom =
      HasFunctorialCofiber.cofibι (completion.map f) := classicalCompletionConstruction.completion_cofiber_inclusion f

public theorem completion_cofiber_boundary {X Y : Ordinary.Spectrum} (f : X ⟶ Y) :
    completion.map (HasFunctorialCofiber.cofibδ f) ≫ (completionShiftIso 1).hom.app X =
      (completionCofiberIso f).hom ≫ HasFunctorialCofiber.cofibδ (completion.map f) := classicalCompletionConstruction.completion_cofiber_boundary f

public def completionSphereShiftIso (n : ℤ) :
    completion.obj (Sphere (C := Ordinary.Spectrum) n) ≅ (Sphere (C := Spectrum) n) :=
  (completionShiftIso n).app _ ≪≫ (shiftFunctor Spectrum n).mapIso completionSphereIso

end
end KIP126.AdamsSynthetic.Completed
