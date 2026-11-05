module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Tail.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyFunctor.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.FiniteSupport.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Generators
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Path.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

theorem freeEvaluation_id (n : ℕ) (A : BasedSpace.{u}) :
    freeEvaluation n A (free n A) (𝟙 _) = eqToHom (free_level n A).symm := by
  apply BasedSpace.Hom.ext
  have h := (freeEvaluation_exists n A (free n A)).choose_spec (𝟙 _)
  have hc (B : BasedSpace.{u}) (hB : B = A) :
      HEq (ContinuousMap.id B) (BasedSpace.Hom.map (eqToHom hB.symm)) := by
    subst B
    rfl
  exact eq_of_heq (h.trans (hc _ (free_level n A)))

end KIP126.AdamsSynthetic.Source.Prespectrum
