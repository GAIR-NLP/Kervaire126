module

public import KIP126.AdamsSynthetic.Completed.Background
public import KIP126.AdamsSynthetic.ModelPresentation

/-! Derived comparisons and functorial cofibers of the fixed model presentations.
The category structures, triangulations and cofiber comparisons come from
the same model constructions. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory KIP126.StableHomotopy HomotopicalAlgebra
noncomputable section

public def spectrumHomotopyEquivalence :
    letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
    letI := spectrumModelPresentation.pointSetCategory
    letI := spectrumModelPresentation.pointSetModel
    @Equivalence (weakEquivalences spectrumModelPresentation.PointSet).Localization Spectrum
      inferInstance spectrumCategory.toCategory :=
  by
    letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
    exact spectrumModelPresentation.shrinkHoms.toStableModelPresentation.homotopyEquivalence

public def spectrumLocalizationComparison :
    letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
    letI := spectrumModelPresentation.pointSetCategory
    letI := spectrumModelPresentation.pointSetModel
    (weakEquivalences spectrumModelPresentation.PointSet).Q ⋙
      spectrumHomotopyEquivalence.functor ≅ spectrumModelPresentation.shrinkHoms.localization :=
  by
    letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
    exact spectrumModelPresentation.shrinkHoms.toStableModelPresentation.localizationComparison

public def syntheticHomotopyEquivalence :
    letI := syntheticModelPresentation.pointSetCategory
    letI := syntheticModelPresentation.pointSetModel
    (weakEquivalences syntheticModelPresentation.PointSet).Localization ≌ SyntheticSpectrum :=
  syntheticModelPresentation.toStableModelPresentation.homotopyEquivalence

public def syntheticLocalizationComparison :
    letI := syntheticModelPresentation.pointSetCategory
    letI := syntheticModelPresentation.pointSetModel
    (weakEquivalences syntheticModelPresentation.PointSet).Q ⋙
      syntheticHomotopyEquivalence.functor ≅ syntheticModelPresentation.localization :=
  syntheticModelPresentation.toStableModelPresentation.localizationComparison

/-- The functorial cofiber constructed from the fixed classical point-set
model and then sent to the same fixed category of spectra. Its source
retains actual point-set squares. -/
public def spectrumModelCofiber :
    letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
    letI := spectrumModelPresentation.pointSetCategory
    letI := spectrumModelPresentation.pointSetModel
    @CategoryTheory.Functor (Arrow spectrumModelPresentation.PointSet) inferInstance Spectrum spectrumCategory.toCategory :=
  by
    letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
    exact spectrumModelPresentation.shrinkHoms.toStableModelPresentation.localizedCofiberFunctor

/-- The corresponding constructed cofiber for the fixed synthetic model.
Both cofibers use the specified cofibrant generation data. -/
public def syntheticModelCofiber :
    letI := syntheticModelPresentation.pointSetCategory
    letI := syntheticModelPresentation.pointSetModel
    Arrow syntheticModelPresentation.PointSet ⥤ SyntheticSpectrum :=
  syntheticModelPresentation.toStableModelPresentation.localizedCofiberFunctor

end
end KIP126.AdamsSynthetic.Completed
