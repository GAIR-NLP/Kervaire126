module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Support.Topology.Path.Translation.Pointed.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Support.Topology.Path.Translation.HomotopyGroup.Proofs

@[expose] section

namespace KIP126.Topology
universe u v
set_option backward.isDefEq.respectTransparency false

/-- The actual pointed loop map preserves its specified constant loop. -/
theorem continuousBasedLoopMap_point {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (a : X) (b : Y) (h : f a = b) :
    continuousBasedLoopMap f a b h (Path.refl a) = Path.refl b := by
  apply Path.ext
  funext t
  exact h

/-- The all-basepoint comparison for actual loop maps, retaining
an independently named target basepoint and its actual equality. -/
theorem continuousBasedLoopMap_homotopy_bijective_at_all_points
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (a : X) (b : Y) (h : f a = b) (n : ℕ)
    (hπ : Function.Bijective (continuousHomotopyMap (continuousBasedLoopMap f a b h)
      (Path.refl a) (Path.refl b) (continuousBasedLoopMap_point f a b h) n))
    (p : Path a a) :
    Function.Bijective (continuousHomotopyMap (continuousBasedLoopMap f a b h) p
      (continuousBasedLoopMap f a b h p) rfl n) := by
  subst b
  exact continuousLoopMap_homotopy_bijective_at_all_points f a n hπ p

end KIP126.Topology
