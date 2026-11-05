module
public import KIP126.AdamsSynthetic.Ordinary.TopologicalComparison
public import KIP126.AdamsSynthetic.ModelPresentation

/-! The HF₂-localized spectrum category and the νHF₂-localized synthetic category
(Pstrągowski §5.1). The ordinary source and integer homotopy are defined in
`Ordinary`. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open CategoryTheory.MonoidalCategory
noncomputable section

public abbrev CompletedSpectrumSource := ClassicalHF2LocalizedSource Ordinary.sourceComparison
public def Spectrum : Type 1 := CompletedSpectrumSource
public def spectrumModelPresentation :
    SpectrumModelPresentation.{1,0,1,1} CompletedSpectrumSource := by sorry
public instance spectrumCategory : StableHomotopyCategory.{1,0} Spectrum := by
  letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
  exact spectrumModelPresentation.shrinkHoms.stableCategory

/-- Shrinking changes only Hom universes in the already completed source. -/
public def spectrumSourceEquivalence :
    @Equivalence CompletedSpectrumSource Spectrum inferInstance spectrumCategory.toCategory := by
  letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
  exact spectrumModelPresentation.smallHomEquivalence
public theorem spectrumSourceEquivalence_obj (X : CompletedSpectrumSource) :
    spectrumSourceEquivalence.functor.obj X = X := rfl

/-- The ordinary-to-HF₂-completed localization functor. -/
public def completion : Ordinary.Spectrum ⥤ Spectrum :=
  Ordinary.sourceComparison.equivalence.inverse ⋙
    classicalHF2Localization Ordinary.sourceComparison ⋙ spectrumSourceEquivalence.functor

/-- The actual class of νHF₂ equivalences in ordinary synthetic spectra. -/
public def syntheticHF2Equivalences : MorphismProperty Ordinary.SyntheticSpectrum :=
  fun _ _ f => IsIso ((tensorLeft (Ordinary.nu.functor.obj Ordinary.coefficients.object)).map f)
public abbrev CompletedSyntheticSource := syntheticHF2Equivalences.Localization
public def SyntheticSpectrum : Type 1 := CompletedSyntheticSource
public def syntheticSourceModelPresentation :
    SpectrumModelPresentation.{1,0,1,1} CompletedSyntheticSource := by sorry

/-- Bigrading and λ on the small-Hom model of the νHF₂ localization. -/
public def syntheticModelPresentation :
    SyntheticModelPresentation.{1,0,1,0} SyntheticSpectrum := by
  letI := syntheticSourceModelPresentation.toStableModelPresentation.locallySmall
  exact {
    category := syntheticSourceModelPresentation.shrinkHoms.stableCategory.toCategory
    model := syntheticSourceModelPresentation.shrinkHoms
    biShift := by sorry
    biShift_comp := by sorry
    biShift_zero := by sorry
    biShift_compat := by sorry
    biShift_fullyFaithful := by sorry
    lam := by sorry
    biShift_tensor_comm := by sorry }
public instance syntheticCategory : SyntheticCategory.{1,0} SyntheticSpectrum :=
  syntheticModelPresentation.syntheticCategory
end
end KIP126.AdamsSynthetic.Completed
