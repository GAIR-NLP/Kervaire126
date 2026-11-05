module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Replacement.Cubical.Lifting.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits
open KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

/-- Initial left lifting properties assemble over the actual strict
coproduct, without any stability assertion about coproducts. -/
theorem coproduct_initial_hasLiftingProperty {J : Type u} (X : J → Prespectrum.{u})
    {E B : Prespectrum.{u}} (q : E ⟶ B)
    (hX : ∀ j, HasLiftingProperty (zeroMap zeroPrespectrum (X j)) q) :
    HasLiftingProperty (zeroMap zeroPrespectrum (∐ X)) q := by
  letI := hX
  constructor
  intro t b sq
  let sq' (j : J) : CommSq t (zeroMap zeroPrespectrum (X j)) q (Sigma.ι X j ≫ b) :=
    ⟨zeroPrespectrum_isZero.eq_of_src _ _⟩
  refine CommSq.HasLift.mk' {
    l := Sigma.desc (fun j => (sq' j).lift)
    fac_left := zeroPrespectrum_isZero.eq_of_src _ _
    fac_right := ?_ }
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc_assoc]
  exact (sq' j).fac_right

end KIP126.AdamsSynthetic.Source.Prespectrum
