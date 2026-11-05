module

public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basic
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basic
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band0
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band0
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band1
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band1
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band2
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band2
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band3
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band3
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band4
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band4
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band5
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band5
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band6
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band6
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band7
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis.Band7

/-! Complete ordered Cν E₂ basis labels from the fixed t ≤ 200 archive.
The eight source leaves cover t = 0,...,200. All 14,989 labels and 5,588
nonzero bidegrees retain their original order. Absent bidegrees and t > 200
use the archive's empty-list convention. -/

set_option backward.privateInPublic true

@[expose] section
namespace KIP126.Computation.NuCofiberArchive
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

private def basisRowsByT : List (List (ℕ × List String)) :=
  basisBand0 ++
  basisBand1 ++
  basisBand2 ++
  basisBand3 ++
  basisBand4 ++
  basisBand5 ++
  basisBand6 ++
  basisBand7

private def lookupBasisRow (s : ℕ) : List (ℕ × List String) → List String
  | [] => []
  | (rowS, labels) :: rows =>
    match Nat.beq s rowS with
    | true => labels
    | false => lookupBasisRow s rows

private def monomials (s t : ℕ) : List String :=
  match archiveListLookup? basisRowsByT t with
  | none => []
  | some rows => lookupBasisRow s rows

private def basisCount (s t : ℕ) : ℕ := (monomials s t).length

end KIP126.Computation.NuCofiberArchive
