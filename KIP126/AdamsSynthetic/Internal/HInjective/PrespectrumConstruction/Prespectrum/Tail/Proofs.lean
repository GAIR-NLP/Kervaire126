module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Tail.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Suspension.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyFunctor.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

theorem free_succ (n : ℕ) (A : BasedSpace.{u}) :
    free (n+1) A = desuspension (free n A) :=
  Function.iterate_succ_apply' desuspension n (suspensionSpectrum A)

end KIP126.AdamsSynthetic.Source.Prespectrum
