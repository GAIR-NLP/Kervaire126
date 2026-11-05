module

import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Replacement.Spectra.BasedSpace.Under.Data
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.Topology.Category.TopCat.Limits.Basic

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory CategoryTheory.Limits

universe u

/-- Actual based spaces have all small colimits, including the common
basepoint identifications in coproducts and pushouts. -/
noncomputable instance hasColimits : HasColimitsOfSize.{u,u} BasedSpace.{u} :=
  Adjunction.has_colimits_of_equivalence underEquivalence.functor

end KIP126.AdamsSynthetic.Source.BasedSpace
