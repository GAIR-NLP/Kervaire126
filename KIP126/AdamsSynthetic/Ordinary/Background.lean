module

public import KIP126.AdamsSynthetic.Ordinary.Foundations
public import KIP126.AdamsSynthetic.AdamsBackground
public import KIP126.AdamsSynthetic.Context
public import KIP126.AdamsSynthetic.Families
public import KIP126.AdamsSynthetic.Sphere
public import KIP126.AdamsSynthetic.Configuration
public import KIP126.SpectralSequence
public import KIP126.AdamsSynthetic.SphereData
public import KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Source

/-! The classical and synthetic background induced by the model presentations and
comparisons. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Ordinary
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route
noncomputable section

/-- Classical cofibers and square completions from the specified
pretriangulation. Source and completion comparisons use these same choices. -/
public instance spectrumCofiber : HasFunctorialCofiber (C := Spectrum) :=
  HasFunctorialCofiber.ofPretriangulated

/-- The ordinary mod-two coefficient spectrum, before completion. -/
public def coefficients : ModTwoCoefficients Spectrum := by sorry
/-- The ordinary synthetic analogue functor. -/
public def nu : NuFunctorData Spectrum SyntheticSpectrum := by sorry
/-- Ordinary Hopf maps and detector spectrum, before completion. -/
public def auxiliary : AuxiliaryData Spectrum (coefficients := coefficients) := by sorry
end
end KIP126.AdamsSynthetic.Ordinary
