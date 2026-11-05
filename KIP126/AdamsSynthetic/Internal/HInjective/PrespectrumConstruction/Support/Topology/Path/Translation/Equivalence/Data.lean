module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Support.Topology.Path.Translation.Proofs
import Mathlib.Topology.Homotopy.Equiv

@[expose] section

namespace KIP126.Topology
universe u

/-- Actual translation is a homotopy equivalence of the full loop
space, using the reversed loop as its inverse. -/
noncomputable def loopLeftTranslateHomotopyEquiv
    {X : Type u} [TopologicalSpace X] {a : X} (p : Path a a) :
    ContinuousMap.HomotopyEquiv (Path a a) (Path a a) where
  toFun := loopLeftTranslate p
  invFun := loopLeftTranslate p.symm
  left_inv := loopLeftTranslate_symm_comp_homotopic p
  right_inv := loopLeftTranslate_comp_symm_homotopic p

end KIP126.Topology
