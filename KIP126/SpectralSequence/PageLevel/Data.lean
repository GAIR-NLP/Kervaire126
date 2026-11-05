module

public import Mathlib.Data.Int.Basic

@[expose] section

namespace KIP126.Core.SpectralSequence

/-- An admissible displayed Adams page, with its lower bound stored as data. -/
public structure AdamsPage where
  value : ℕ
  valid : 2 ≤ value
  deriving DecidableEq

namespace AdamsPage

/-- The second page of the Adams spectral sequence. -/
public def two : AdamsPage := ⟨2, le_rfl⟩

public def toNat (r : AdamsPage) : ℕ := r.value

public def toInt (r : AdamsPage) : ℤ := r.value

/-- Construct an Adams page from a natural number with an explicit
admissibility proof. -/
public def ofNat (r : ℕ) (hr : 2 ≤ r) : AdamsPage := ⟨r, hr⟩

/-- An integer defines an Adams page only with a proof of the lower bound. -/
public def ofInt (r : ℤ) (hr : 2 ≤ r) : AdamsPage :=
  ⟨r.toNat, by simpa using Int.toNat_le_toNat hr⟩

end AdamsPage

/-- An extension spectral-sequence length. Zero is allowed, so the Adams
page lower bound is not imposed. -/
public structure ExtensionLength where
  value : ℕ
  deriving DecidableEq

namespace ExtensionLength

public def zero : ExtensionLength := ⟨0⟩

public def ofNat (n : ℕ) : ExtensionLength := ⟨n⟩

public def toNat (n : ExtensionLength) : ℕ := n.value

public def toInt (n : ExtensionLength) : ℤ := n.value

/-- Interpret an extension length as an Adams page when it is at least two. -/
public def toAdamsPage (n : ExtensionLength) (hn : 2 ≤ n.value) : AdamsPage :=
  ⟨n.value, hn⟩

end ExtensionLength

namespace AdamsPage

/-- Interpret an Adams page number as an extension length. -/
public def toExtensionLength (r : AdamsPage) : ExtensionLength := ⟨r.value⟩

end AdamsPage

public structure PageLevelConvention where
  firstPage : ℕ
  admissibleFrom : ℤ
  page : ℕ → ℤ
  cycleLevel : ℕ → ℤ
  quotientExponent : ℕ → ℤ
  page_first : page firstPage = admissibleFrom
  page_succ : ∀ r, page (r + 1) = page r + 1
  cycle_succ : ∀ r, cycleLevel (r + 1) = cycleLevel r + 1
  quotient_succ : ∀ r, quotientExponent (r + 1) = quotientExponent r + 1
  cycleLevel_eq_quotientExponent : ∀ r,
    cycleLevel r = quotientExponent r

namespace PageLevelConvention

/-- Read the underlying integer page at an Adams page. -/
public def pageAtAdams (P : PageLevelConvention) (r : AdamsPage) : ℤ :=
  P.page r.toNat

/-- Read the underlying integer page at an extension length. -/
public def pageAtExtension (P : PageLevelConvention) (n : ExtensionLength) : ℤ :=
  P.page n.toNat

end PageLevelConvention

end KIP126.Core.SpectralSequence
