module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Functor.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Zero.Instances
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Free.Proofs
import Mathlib.Algebra.Category.Grp.Preadditive

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory CategoryTheory.Limits

universe u

/-- A constant point-set morphism induces the zero map on the actual stable groups. -/
theorem Prespectrum.stableHomotopyMap_zero_morphism (X Y : Prespectrum.{u}) (d : ℤ)
    (x : X.StableHomotopy d) : stableHomotopyMap (0 : X ⟶ Y) d x = 0 := by
  induction x using Quot.inductionOn with
  | h a => exact loopClass_const Y d a.stage a.dimension a.degree

instance Prespectrum.stableHomotopyAddFunctor_preservesZeroMorphisms (d : ℤ) :
    (stableHomotopyAddFunctor.{u} d).PreservesZeroMorphisms where
  map_zero X Y := by
    ext x
    exact stableHomotopyMap_zero_morphism X Y d x

instance sourceStableHomotopyAddFunctor_preservesZeroMorphisms (d : ℤ) :
    (sourceStableHomotopyAddFunctor.{u} d).PreservesZeroMorphisms where
  map_zero X Y := by
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    change (sourceStableHomotopyAddFunctor d).map
      (0 : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) = _
    rw [← sourceLocalization.map_zero X Y, sourceStableHomotopyAddFunctor_map]
    exact (Prespectrum.stableHomotopyAddFunctor d).map_zero X Y

end KIP126.AdamsSynthetic.Source
