module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Map.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyFunctor.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Stabilized.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Spectrification.Stabilization.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

variable {J : Type}

/-- The constructed telescope satisfies bijective actual stabilization. -/
theorem spectrificationTelescope_hasBijectiveStabilization (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] : HasBijectiveStabilization (spectrificationTelescope X) :=
  spectrificationTelescope_stabilize_bijective X

end KIP126.AdamsSynthetic.Source.Prespectrum
