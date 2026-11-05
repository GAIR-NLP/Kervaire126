module

import all KIP126.AdamsSynthetic.Internal.HInjective.SphereLifting
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Replacement.Cubical.Cofibrant.Predicates

@[expose] section
namespace KIP126.AdamsSynthetic.Source.Prespectrum

/-- The fixed actual sphere, with its original Fin 2 level and suspension
bonds, has the full cubical left lifting property. No replacement is chosen. -/
private theorem actual_sphere_isCubicallyCofibrant :
    IsCubicallyCofibrant (sphere : Prespectrum.{0}) := by
  intro E B p hp
  exact sphere_initial_hasLiftingProperty_of_level p hp


end KIP126.AdamsSynthetic.Source.Prespectrum
end
