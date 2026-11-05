module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyFunctor.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory TypeCat

universe u

@[simp] theorem sourceStableHomotopyFunctor_fac (d : ℤ) :
    sourceLocalization ⋙ sourceStableHomotopyFunctor.{u} d =
      Prespectrum.stableHomotopyFunctor d :=
  Localization.Construction.fac _ _

/-- On an actual point-set map, the descended functor is the originally
specified map of the cubical stable quotient. -/
@[simp] theorem sourceStableHomotopyFunctor_map
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    (sourceStableHomotopyFunctor d).map (sourceLocalization.map f) =
      ofHom (Prespectrum.stableHomotopyMap f d) := by
  have h : ∀ (F G : Prespectrum.{u} ⥤ Type u), F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (h _ _ (sourceStableHomotopyFunctor_fac d))

/-- The original definition of stable equivalence is saturated on
point-set maps by the specified ordinary localization. -/
theorem Prespectrum.stableEquivalence_iff_source_isIso
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences f ↔ IsIso (sourceLocalization.map f) := by
  constructor
  · exact stableEquivalences.Q_inverts f
  · intro hf d
    letI := hf
    have hi : IsIso ((sourceStableHomotopyFunctor d).map (sourceLocalization.map f)) :=
      inferInstance
    rw [sourceStableHomotopyFunctor_map] at hi
    exact (bijective_iff_isIso_ofHom _).mpr hi

end KIP126.AdamsSynthetic.Source
