module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Replacement.Cubical.Cofibrant.Predicates
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Path.Endpoint.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- The lifting property gives exact strict lifts of actual maps. -/
theorem IsCubicallyCofibrant.lift {X : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    {E B : Prespectrum.{u}} (p : E ⟶ B) (hp : ∀ n,HasCubeBoundaryLifting (p.level n))
    (b : X ⟶ B) : ∃ l : X ⟶ E, l ≫ p = b := by
  letI := hX p hp
  let sq : CommSq (zeroMap zeroPrespectrum E) (zeroMap zeroPrespectrum X) p b :=
    ⟨zeroPrespectrum_isZero.eq_of_src _ _⟩
  exact ⟨sq.lift,sq.fac_right⟩

/-- A spectrum with actual left lifting is a strict retract of its
actual free-cell replacement. -/
theorem IsCubicallyCofibrant.replacement_hasSection {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) :
    ∃ s : X ⟶ cubicalReplacementFunctor.obj X,
      s ≫ cubicalReplacementComparison.app X = 𝟙 X :=
  hX.lift (cubicalReplacementComparison.app X)
    (cubicalReplacementComparison_level_hasCubeBoundaryLifting X) (𝟙 X)

end KIP126.AdamsSynthetic.Source.Prespectrum
