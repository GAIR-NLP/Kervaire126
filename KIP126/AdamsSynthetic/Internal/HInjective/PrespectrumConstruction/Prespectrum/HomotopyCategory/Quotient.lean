module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] section

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u

/-- The homotopy category of strict prespectra, quotienting precisely by
actual based homotopies compatible with all bonding maps. -/
abbrev HomotopyCategory := CategoryTheory.Quotient pathHomotopic.{u}

/-- The identity-on-objects quotient by the actual homotopy congruence. -/
def homotopyQuotient : Prespectrum.{u} ⥤ HomotopyCategory.{u} :=
  CategoryTheory.Quotient.functor pathHomotopic

/-- The original ordinary stable localization factors through actual homotopy. -/
noncomputable def homotopyToSource : HomotopyCategory.{u} ⥤ SourceCategory.{u} :=
  CategoryTheory.Quotient.lift pathHomotopic sourceLocalization
    (fun _ _ _ _ h => source_map_eq_of_pathHomotopic h)

/-- Actual stable equivalences descended through the homotopy congruence. -/
def homotopyStableEquivalences : MorphismProperty HomotopyCategory.{u} :=
  stableEquivalences.quotient pathHomotopic

end KIP126.AdamsSynthetic.Source.Prespectrum

end

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u

/-- Equality in the quotient is equivalent to the existence of a strict path
homotopy. -/
theorem homotopyQuotient_map_eq_iff {X Y : Prespectrum.{u}} (f g : X ⟶ Y) :
    homotopyQuotient.map f = homotopyQuotient.map g ↔ pathHomotopic f g :=
  CategoryTheory.Quotient.functor_map_eq_iff pathHomotopic f g

@[simp] theorem homotopyToSource_fac :
    homotopyQuotient.{u} ⋙ homotopyToSource = sourceLocalization :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp] theorem homotopyStableEquivalences_map_iff {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    homotopyStableEquivalences (homotopyQuotient.map f) ↔ stableEquivalences f :=
  stableEquivalences.quotient_iff pathHomotopic f

/-- Every quotient morphism still has an actual strict representative. -/
theorem homotopyQuotient_map_surjective {X Y : Prespectrum.{u}}
    (f : homotopyQuotient.obj X ⟶ homotopyQuotient.obj Y) :
    ∃ g : X ⟶ Y, homotopyQuotient.map g = f :=
  CategoryTheory.Quotient.full_functor pathHomotopic |>.map_surjective f

/-- The descended functor inverts the actual stable equivalences on the quotient. -/
theorem homotopyToSource_inverts : homotopyStableEquivalences.{u}.IsInvertedBy homotopyToSource := by
  rintro ⟨X⟩ ⟨Y⟩ f ⟨g,hg,rfl⟩
  exact stableEquivalences.Q_inverts g hg

end KIP126.AdamsSynthetic.Source.Prespectrum

end
