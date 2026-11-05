module

public import KIP126.AdamsSynthetic.Source
public import KIP126.AdamsSynthetic.ModelPresentation

/-! The fixed object types and their model presentations.
Each category structure is derived from the model localizing to that same type. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Ordinary
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
noncomputable section
set_option backward.privateInPublic true

/-- The ordinary synthetic object type and its presentation are chosen by
one source construction. The existing model record carries its category,
stable monoidal structure, bigrading and deformation map. -/
private structure SyntheticSourceData where
  objects : Type 1
  modelPresentation : SyntheticModelPresentation.{1,0,1,0} objects

private def syntheticSourceConstruction : SyntheticSourceData where
  objects := by sorry
  modelPresentation := by sorry

/-- The ordinary stable localization of the concrete prespectrum source. -/
public def Spectrum : Type 1 := ClassicalSource
/-- The category of HF₂-synthetic spectra. -/
public def SyntheticSpectrum : Type 1 := syntheticSourceConstruction.objects

/-- The primitive pointed cofibrantly generated symmetric monoidal model,
localizing to the raw large-Hom category of ordinary spectra. Its canonically
shrunk model supplies the small-Hom category. -/
public def spectrumModelPresentation :
    @SpectrumModelPresentation.{1,0,1,1} ClassicalSource classicalSourceCategory := by sorry

/-- The synthetic source category, its primitive stable monoidal model, and
its additional bigrading and deformation map. No target triangulation is input. -/
public def syntheticModelPresentation :
    SyntheticModelPresentation.{1,0,1,0} SyntheticSpectrum :=
  syntheticSourceConstruction.modelPresentation

public instance spectrumCategory : StableHomotopyCategory.{1,0} Spectrum := by
  letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
  exact spectrumModelPresentation.shrinkHoms.stableCategory

public instance syntheticCategory : SyntheticCategory.{1,0} SyntheticSpectrum :=
  syntheticModelPresentation.syntheticCategory

/-- The raw stable source and the fixed small-Hom spectrum category have the
same objects, with their morphisms related by the canonical shrinking equivalence. -/
public def spectrumSourceEquivalence :
    @Equivalence ClassicalSource Spectrum classicalSourceCategory spectrumCategory.toCategory := by
  letI := spectrumModelPresentation.toStableModelPresentation.locallySmall
  exact spectrumModelPresentation.smallHomEquivalence

/-- The source comparison is the identity on spectrum objects. -/
public theorem spectrumSourceEquivalence_obj (X : ClassicalSource) :
    spectrumSourceEquivalence.functor.obj X = X := rfl

end
end KIP126.AdamsSynthetic.Ordinary
