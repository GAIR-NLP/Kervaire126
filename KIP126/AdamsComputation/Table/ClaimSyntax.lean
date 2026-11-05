module

public import KIP126.AdamsComputation.Table.Syntax

/-! Finite computation syntax. -/

@[expose] section
namespace KIP126.Computation.Table.Raw
public inductive Kind where
  | equation | reaches | boundaryBy | refutation
  deriving DecidableEq, BEq, Repr
public structure Claim where
  spectrum : Spectrum
  kind : Kind
  r : Nat
  s : Nat
  t : Nat
  x : List Nat
  ts : Nat
  tt : Nat
  /-- Target coordinates for equations and refutations; ignored for
`reaches` and `boundaryBy`. -/
  y : List Nat
  deriving DecidableEq, BEq, Repr
/-- Syntactic validity and degree compatibility of a claim. -/
public def Claim.valid (degrees : List Degree) (c : Claim) : Bool :=
  2 ≤ c.r && coordinatesValid degrees c.spectrum c.s c.t c.x &&
    match c.kind with
    | .reaches | .boundaryBy => true
    | .equation | .refutation => c.ts == c.s + c.r && c.tt == c.t + c.r - 1 &&
        coordinatesValid degrees c.spectrum c.ts c.tt c.y
end KIP126.Computation.Table.Raw
