module

/-! Finite computation syntax. -/

@[expose] section
namespace KIP126.Computation.Table.Raw
public inductive Spectrum where
  | sphere | nuCofiber
  deriving DecidableEq, BEq, Repr
public structure Degree where
  spectrum : Spectrum
  s : Nat
  t : Nat
  monomials : List String
  deriving DecidableEq, BEq, Repr
public structure Product where
  s : Nat
  t : Nat
  sp : Nat
  tp : Nat
  deriving DecidableEq, BEq, Repr
public structure BottomMap where
  s : Nat
  t : Nat
  x : List Nat
  y : List Nat
  deriving DecidableEq, BEq, Repr

/-- Check the degree lookup and strictly increasing, in-range coordinate indices. -/
public def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a < b && strictlyIncreasing (b :: rest)

public def coordinatesValid (degrees : List Degree) (o : Spectrum)
    (s t : Nat) (indices : List Nat) : Bool :=
  match degrees.find? (fun d => d.spectrum == o && d.s == s && d.t == t) with
  | none => false
  | some d => indices.all (· < d.monomials.length) && strictlyIncreasing indices

end KIP126.Computation.Table.Raw
