module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import Mathlib.Topology.Path

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Topology
open scoped unitInterval
universe u

/-- The actual compact-open space of based loops, based at the constant loop. -/
abbrev loopLevel (A : BasedSpace.{u}) : BasedSpace.{u} where
  space := TopCat.of (Path A.point A.point)
  point := Path.refl A.point

/-- Apply the original structure map pointwise to a based loop. -/
def loopBond (X : Prespectrum.{u}) (n : ℕ) :
    C(loopLevel (X.level n) × I, loopLevel (X.level (n+1))) where
  toFun z :=
    { toFun s := X.bond n (z.1 s,z.2)
      continuous_toFun := (X.bond n).continuous.comp
        (z.1.continuous.prodMk continuous_const)
      source' := by rw [Path.source,X.bond_point]
      target' := by rw [Path.target,X.bond_point] }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    ((X.bond n).continuous.comp
      ((continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
        continuous_fst.snd))

/-- The genuine pointwise loop prespectrum. -/
abbrev loop (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := loopLevel (X.level n)
  bond := loopBond X
  bond_point n t := by
    apply Path.ext
    funext s
    exact X.bond_point n t
  bond_zero n p := by
    apply Path.ext
    funext s
    exact X.bond_zero n (p s)
  bond_one n p := by
    apply Path.ext
    funext s
    exact X.bond_one n (p s)

/-- The actual pointwise map on based loops. -/
def loopMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) : loop X ⟶ loop Y where
  level n :=
    { toFun p :=
        { toFun s := f.level n (p s)
          continuous_toFun := (f.level n).continuous.comp p.continuous
          source' := by rw [Path.source,f.point]
          target' := by rw [Path.target,f.point] }
      continuous_toFun := Path.continuous_uncurry_iff.mp
        ((f.level n).continuous.comp continuous_eval) }
  point n := by
    apply Path.ext
    funext s
    exact f.point n
  bond n p t := by
    apply Path.ext
    funext s
    exact f.bond n (p s) t

end KIP126.AdamsSynthetic.Source.Prespectrum
