module

import Mathlib.Data.Nat.Basic

/-! Complete bounded Cν comparison range. Every s and t ≤ 200 is included,
also when the basis is empty. Selected finite equations are defined in Table. -/
set_option backward.privateInPublic true

@[expose] section
namespace KIP126.Computation.NuCofiberArchive

private abbrev InScope (_s t : ℕ) : Prop := t ≤ 200

end KIP126.Computation.NuCofiberArchive
