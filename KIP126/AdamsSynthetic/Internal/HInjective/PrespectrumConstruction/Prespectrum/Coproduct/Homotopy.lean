module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Colimit.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyCategory.Homotopy.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] section

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- Assemble actual strict homotopies by the universal property of the strict
coproduct, with the actual path prespectrum as target. -/
noncomputable def StrictHomotopy.coproduct {J : Type u} {X : J → Prespectrum.{u}}
    {Y : Prespectrum.{u}} {f g : (∐ X) ⟶ Y}
    (H : ∀ j, StrictHomotopy (Sigma.ι X j ≫ f) (Sigma.ι X j ≫ g)) :
    StrictHomotopy f g where
  hom := Sigma.desc (fun j => (H j).hom)
  zero := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_desc_assoc]
    exact (H j).zero
  one := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_desc_assoc]
    exact (H j).one

end KIP126.AdamsSynthetic.Source.Prespectrum

end

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- Homotopy out of the actual strict coproduct is detected independently
on all summands. -/
theorem pathHomotopic_coproduct_iff {J : Type u} {X : J → Prespectrum.{u}}
    {Y : Prespectrum.{u}} (f g : (∐ X) ⟶ Y) :
    pathHomotopic f g ↔ ∀ j, pathHomotopic (Sigma.ι X j ≫ f) (Sigma.ι X j ≫ g) := by
  constructor
  · rintro ⟨H⟩ j
    exact ⟨H.precomp (Sigma.ι X j)⟩
  · intro H
    exact ⟨StrictHomotopy.coproduct (fun j => Classical.choice (H j))⟩

end KIP126.AdamsSynthetic.Source.Prespectrum

end
