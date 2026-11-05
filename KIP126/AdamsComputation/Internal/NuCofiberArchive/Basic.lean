module

import Mathlib.Data.Nat.Basic

/-! Source-table types and structural lookup. -/

set_option backward.privateInPublic true

@[expose] section
namespace KIP126.Computation.NuCofiberArchive
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

private abbrev SourceRows := List (List (ℕ × List String))

universe u

/- Structural lookup avoids proof-bearing bounded-index operations. -/
private def archiveListLookup? {α : Type u} : List α → ℕ → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, i + 1 => archiveListLookup? tail i

end KIP126.Computation.NuCofiberArchive
