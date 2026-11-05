module

import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Replacement.Spectra.Prespectrum.Tail.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

noncomputable def freeStabilization : ∀ (n : ℕ) (A : BasedSpace.{u}),
    free (n+1) A.suspension ⟶ free n A
  | 0, A => eqToHom (congrArg desuspension (suspensionSpectrum_tail A)) ≫
      paddedTailInclusion (suspensionSpectrum A)
  | n+1, A => eqToHom (free_succ (n+1) A.suspension) ≫
      desuspensionMap (freeStabilization n A) ≫ eqToHom (free_succ n A).symm

end KIP126.AdamsSynthetic.Source.Prespectrum
