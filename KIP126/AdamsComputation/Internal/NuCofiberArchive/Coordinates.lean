module

public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basic
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basic
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Finite coordinate spaces and unit vectors indexed by the ordered basis labels. -/

set_option backward.privateInPublic true

@[expose] section
namespace KIP126.Computation.NuCofiberArchive
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/- Source vectors carry the original ordered basis addresses, including the
zero-dimensional spaces of missing bidegrees and degrees above t = 200. -/
private abbrev Coordinate (s t : ℕ) := Fin (basisCount s t) →₀ ZMod 2

private noncomputable def basisVector (s t : ℕ) (i : Fin (basisCount s t)) :
    Coordinate s t :=
  Finsupp.single i 1

private theorem basisVector_apply_self (s t : ℕ) (i : Fin (basisCount s t)) :
    basisVector s t i i = 1 :=
  Finsupp.single_eq_same

private theorem basisVector_ne_zero (s t : ℕ) (i : Fin (basisCount s t)) :
    basisVector s t i ≠ 0 := by
  intro h
  have h10 : (1 : ZMod 2) = 0 := by
    simpa only [basisVector, Finsupp.single_eq_same, Finsupp.zero_apply] using
      congrArg (fun v : Coordinate s t => v i) h
  exact one_ne_zero h10

private noncomputable def coordinateBasis (s t : ℕ) :
    Module.Basis (Fin (basisCount s t)) (ZMod 2) (Coordinate s t) :=
  Finsupp.basisSingleOne

private theorem coordinateBasis_apply (s t : ℕ) (i : Fin (basisCount s t)) :
    coordinateBasis s t i = basisVector s t i := by
  simpa only [coordinateBasis, basisVector] using
    congrFun (Finsupp.coe_basisSingleOne (R := ZMod 2)
      (ι := Fin (basisCount s t))) i

private def basisLabel? (s t i : ℕ) : Option String :=
  archiveListLookup? (monomials s t) i

end KIP126.Computation.NuCofiberArchive
