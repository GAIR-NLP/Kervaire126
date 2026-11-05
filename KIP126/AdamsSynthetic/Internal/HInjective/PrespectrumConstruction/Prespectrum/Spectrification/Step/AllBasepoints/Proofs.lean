module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Spectrification.Step.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Stabilized.Map.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Support.Topology.Path.Translation.Pointed.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The same all-basepoint propagation applies to the actual
spectrification step, whose specified level maps are literal loop maps. -/
theorem spectrificationStepMap_level_homotopy_bijective_at_all_points
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (hf : Function.Bijective ((spectrificationStepMap f).levelHomotopy n r))
    (p : (spectrificationStep X).level n) :
    Function.Bijective (KIP126.Topology.continuousHomotopyMap ((spectrificationStepMap f).level n)
      p ((spectrificationStepMap f).level n p) rfl r) :=
  KIP126.Topology.continuousBasedLoopMap_homotopy_bijective_at_all_points
    (f.level (n+1)) (X.level (n+1)).point (Y.level (n+1)).point (f.point (n+1)) r hf p

end KIP126.AdamsSynthetic.Source.Prespectrum
