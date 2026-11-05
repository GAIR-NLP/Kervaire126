module

public import KIP126.AdamsComputation.Table.Data
public import KIP126.AdamsComputation.Table.D2

/-! Coordinate table for 200 SS inputs. Direct Adams E₂-basis d₂ records
are defined in AdamsComputation.Table.D2. -/

@[expose] section
namespace KIP126.SSComputation.Input

/-- For `moore`, coordinates denote bottom-cell images of sphere basis vectors. -/
public inductive Spectrum where
  | sphere | nuCofiber | moore
  deriving DecidableEq, BEq, Repr

public structure Claim where
  spectrum : Spectrum
  kind : KIP126.Computation.Table.Raw.Kind
  r : Nat
  s : Nat
  t : Nat
  x : List Nat
  ts : Nat
  tt : Nat
  y : List Nat
  deriving DecidableEq, BEq, Repr

/-- Sphere/Cν coordinate projection. Moore coordinates use the bottom-cell map. -/
public def Claim.toRaw? (c : Claim) : Option KIP126.Computation.Table.Raw.Claim :=
  match c.spectrum with
  | .sphere => some ⟨.sphere, c.kind, c.r, c.s, c.t, c.x, c.ts, c.tt, c.y⟩
  | .nuCofiber => some ⟨.nuCofiber, c.kind, c.r, c.s, c.t, c.x, c.ts, c.tt, c.y⟩
  | .moore => none

/-- All 200 distinct finite coordinate inputs, including the zero d₄ on
C₂ and the zero d₇ on sphere coordinates [0,1]. -/
public def claims : List Claim := [
  ⟨.nuCofiber, .equation, 2, 7, 134, [1], 9, 135, [3]⟩,
  ⟨.nuCofiber, .equation, 2, 7, 134, [3], 9, 135, [4]⟩,
  ⟨.nuCofiber, .equation, 3, 8, 135, [0], 11, 137, [0]⟩,
  ⟨.nuCofiber, .equation, 2, 8, 135, [2], 10, 136, [1]⟩,
  ⟨.nuCofiber, .equation, 2, 8, 135, [3], 10, 136, [2]⟩,
  ⟨.nuCofiber, .reaches, 16, 9, 135, [1], 9, 135, []⟩,
  ⟨.nuCofiber, .equation, 4, 9, 135, [2], 13, 138, [3]⟩,
  ⟨.nuCofiber, .equation, 3, 9, 135, [0], 12, 137, [4]⟩,
  ⟨.nuCofiber, .equation, 2, 9, 136, [3], 11, 137, [3]⟩,
  ⟨.nuCofiber, .equation, 3, 10, 136, [0], 13, 138, [1]⟩,
  ⟨.nuCofiber, .equation, 2, 10, 137, [1], 12, 138, [1]⟩,
  ⟨.nuCofiber, .equation, 2, 10, 137, [4], 12, 138, [3]⟩,
  ⟨.nuCofiber, .equation, 3, 8, 134, [0, 3, 4], 11, 136, [3]⟩,
  ⟨.nuCofiber, .reaches, 1000, 11, 137, [1, 2], 11, 137, []⟩,
  ⟨.nuCofiber, .reaches, 14, 11, 137, [2], 11, 137, []⟩,
  ⟨.nuCofiber, .equation, 3, 12, 138, [0], 15, 140, [2]⟩,
  ⟨.nuCofiber, .equation, 2, 12, 138, [2], 14, 139, [3]⟩,
  ⟨.sphere, .equation, 2, 1, 64, [0], 3, 65, [0]⟩,
  ⟨.sphere, .equation, 2, 1, 128, [0], 3, 129, [0]⟩,
  ⟨.sphere, .equation, 2, 2, 65, [0], 4, 66, [0]⟩,
  ⟨.sphere, .reaches, 7, 2, 128, [0], 2, 128, []⟩,
  ⟨.sphere, .equation, 2, 2, 129, [0], 4, 130, [1]⟩,
  ⟨.sphere, .reaches, 1000, 3, 66, [0], 3, 66, []⟩,
  ⟨.sphere, .equation, 2, 3, 66, [1], 5, 67, [2]⟩,
  ⟨.sphere, .reaches, 14, 3, 130, [0], 3, 130, []⟩,
  ⟨.sphere, .equation, 2, 3, 130, [1], 5, 131, [0]⟩,
  ⟨.sphere, .equation, 2, 4, 67, [0], 6, 68, [1]⟩,
  ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0]⟩,
  ⟨.sphere, .equation, 2, 4, 131, [0], 6, 132, [1]⟩,
  ⟨.sphere, .equation, 3, 5, 67, [1], 8, 69, [0]⟩,
  ⟨.sphere, .equation, 2, 5, 67, [0], 7, 68, [0, 1]⟩,
  ⟨.sphere, .equation, 2, 5, 68, [0], 7, 69, [0]⟩,
  ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2]⟩,
  ⟨.sphere, .equation, 2, 5, 132, [0], 7, 133, [1]⟩,
  ⟨.sphere, .reaches, 1000, 6, 68, [0], 6, 68, []⟩,
  ⟨.sphere, .reaches, 1000, 6, 69, [0], 6, 69, []⟩,
  ⟨.sphere, .equation, 2, 6, 69, [1], 8, 70, [2]⟩,
  ⟨.sphere, .equation, 5, 6, 130, [0], 11, 134, [2]⟩,
  ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3]⟩,
  ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4]⟩,
  ⟨.sphere, .reaches, 3, 6, 132, [0], 6, 132, []⟩,
  ⟨.sphere, .reaches, 4, 6, 133, [0], 6, 133, []⟩,
  ⟨.sphere, .equation, 2, 6, 133, [1], 8, 134, [5]⟩,
  ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2]⟩,
  ⟨.sphere, .equation, 3, 7, 131, [0], 10, 133, [0, 1]⟩,
  ⟨.sphere, .reaches, 18, 7, 133, [0], 7, 133, []⟩,
  ⟨.sphere, .equation, 2, 7, 134, [1], 9, 135, [4]⟩,
  ⟨.sphere, .equation, 2, 7, 134, [4], 9, 135, [5]⟩,
  ⟨.sphere, .reaches, 1000, 8, 70, [1], 8, 70, []⟩,
  ⟨.sphere, .reaches, 6, 8, 130, [0], 8, 130, []⟩,
  ⟨.sphere, .equation, 3, 8, 131, [0], 11, 133, [0, 1]⟩,
  ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2]⟩,
  ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0]⟩,
  ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4]⟩,
  ⟨.sphere, .reaches, 17, 8, 134, [4], 8, 134, []⟩,
  ⟨.sphere, .reaches, 6, 8, 134, [0, 3], 8, 134, []⟩,
  ⟨.sphere, .equation, 3, 8, 134, [3], 11, 136, [1]⟩,
  ⟨.sphere, .equation, 3, 8, 134, [2], 11, 136, [2]⟩,
  ⟨.sphere, .equation, 2, 8, 134, [1], 10, 135, [3]⟩,
  ⟨.sphere, .equation, 2, 8, 135, [0], 10, 136, [1]⟩,
  ⟨.sphere, .equation, 2, 8, 135, [4], 10, 136, [3]⟩,
  ⟨.sphere, .equation, 2, 8, 135, [6], 10, 136, [4]⟩,
  ⟨.sphere, .equation, 3, 9, 132, [1], 12, 134, [1, 2]⟩,
  ⟨.sphere, .equation, 3, 9, 133, [1, 2], 12, 135, [0]⟩,
  ⟨.sphere, .equation, 3, 9, 133, [0, 2], 12, 135, [1, 2]⟩,
  ⟨.sphere, .equation, 2, 9, 133, [2], 11, 134, [4]⟩,
  ⟨.sphere, .reaches, 1000, 9, 134, [2], 9, 134, []⟩,
  ⟨.sphere, .reaches, 7, 9, 134, [3], 9, 134, []⟩,
  ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0]⟩,
  ⟨.sphere, .equation, 2, 9, 134, [0], 11, 135, [3, 4]⟩,
  ⟨.sphere, .equation, 2, 9, 134, [4], 11, 135, [4]⟩,
  ⟨.sphere, .equation, 4, 9, 135, [2], 13, 138, [0]⟩,
  ⟨.sphere, .equation, 4, 9, 135, [1], 13, 138, [2]⟩,
  ⟨.sphere, .equation, 3, 9, 135, [0], 12, 137, [3, 4]⟩,
  ⟨.sphere, .equation, 3, 9, 135, [3], 12, 137, [3]⟩,
  ⟨.sphere, .equation, 2, 9, 136, [2], 11, 137, [4]⟩,
  ⟨.sphere, .equation, 2, 9, 136, [4], 11, 137, [5]⟩,
  ⟨.sphere, .equation, 2, 10, 133, [1], 12, 134, [2]⟩,
  ⟨.sphere, .reaches, 1000, 10, 134, [4], 10, 134, []⟩,
  ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1]⟩,
  ⟨.sphere, .equation, 3, 10, 135, [0], 13, 137, [0]⟩,
  ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2]⟩,
  ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4]⟩,
  ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4]⟩,
  ⟨.sphere, .reaches, 1000, 10, 136, [2], 10, 136, []⟩,
  ⟨.sphere, .equation, 2, 10, 137, [0], 12, 138, [0]⟩,
  ⟨.sphere, .equation, 2, 10, 137, [1], 12, 138, [2]⟩,
  ⟨.sphere, .equation, 2, 10, 137, [5], 12, 138, [4]⟩,
  ⟨.sphere, .reaches, 1000, 11, 133, [1], 11, 133, []⟩,
  ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0]⟩,
  ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2]⟩,
  ⟨.sphere, .reaches, 5, 11, 136, [3], 11, 136, []⟩,
  ⟨.sphere, .equation, 4, 11, 136, [0], 15, 139, [0]⟩,
  ⟨.sphere, .equation, 2, 11, 136, [4], 13, 137, [3]⟩,
  ⟨.sphere, .reaches, 1000, 11, 137, [1, 2], 11, 137, []⟩,
  ⟨.sphere, .equation, 4, 11, 137, [2], 15, 140, [1]⟩,
  ⟨.sphere, .equation, 2, 10, 133, [0], 12, 134, [2]⟩,
  ⟨.sphere, .equation, 3, 9, 132, [0], 12, 134, [1]⟩,
  ⟨.sphere, .reaches, 1000, 12, 134, [0], 12, 134, []⟩,
  ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2]⟩,
  ⟨.sphere, .equation, 3, 9, 135, [0, 3], 12, 137, [4]⟩,
  ⟨.sphere, .equation, 2, 12, 137, [1], 14, 138, [4]⟩,
  ⟨.sphere, .equation, 2, 12, 137, [0], 14, 138, [3]⟩,
  ⟨.sphere, .equation, 4, 12, 138, [3], 16, 141, [1]⟩,
  ⟨.sphere, .equation, 2, 12, 138, [1], 14, 139, [2]⟩,
  ⟨.sphere, .equation, 3, 13, 136, [1], 16, 138, [1]⟩,
  ⟨.sphere, .equation, 3, 13, 136, [0], 16, 138, [0, 2]⟩,
  ⟨.sphere, .reaches, 1000, 13, 137, [1], 13, 137, []⟩,
  ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0]⟩,
  ⟨.sphere, .equation, 3, 13, 138, [1], 16, 140, [1]⟩,
  ⟨.sphere, .equation, 5, 13, 139, [0], 18, 143, [0]⟩,
  ⟨.sphere, .equation, 2, 13, 139, [1], 15, 140, [4]⟩,
  ⟨.sphere, .equation, 3, 14, 137, [1], 17, 139, [1]⟩,
  ⟨.sphere, .equation, 3, 14, 137, [0], 17, 139, [0]⟩,
  ⟨.sphere, .reaches, 1000, 14, 139, [1], 14, 139, []⟩,
  ⟨.sphere, .equation, 2, 14, 139, [0], 16, 140, [2]⟩,
  ⟨.sphere, .equation, 2, 14, 140, [1], 16, 141, [2]⟩,
  ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2]⟩,
  ⟨.sphere, .equation, 5, 15, 140, [2], 20, 144, [0]⟩,
  ⟨.sphere, .equation, 2, 15, 140, [0], 17, 141, [3]⟩,
  ⟨.sphere, .equation, 2, 15, 140, [3], 17, 141, [1]⟩,
  ⟨.sphere, .equation, 2, 15, 141, [0], 17, 142, [0]⟩,
  ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2]⟩,
  ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2]⟩,
  ⟨.sphere, .equation, 2, 16, 141, [0], 18, 142, [0, 1]⟩,
  ⟨.sphere, .equation, 2, 16, 141, [3], 18, 142, [1]⟩,
  ⟨.sphere, .equation, 2, 15, 139, [3], 17, 140, [2, 3]⟩,
  ⟨.sphere, .equation, 2, 15, 139, [2, 3], 17, 140, [3]⟩,
  ⟨.sphere, .equation, 2, 17, 142, [1], 19, 143, [1]⟩,
  ⟨.sphere, .equation, 4, 17, 143, [1], 21, 146, [0]⟩,
  ⟨.sphere, .equation, 2, 18, 143, [1], 20, 144, [1]⟩,
  ⟨.sphere, .equation, 2, 18, 144, [0], 20, 145, [1]⟩,
  ⟨.sphere, .equation, 3, 18, 145, [4], 21, 147, [2]⟩,
  ⟨.sphere, .equation, 3, 19, 144, [0], 22, 146, [1]⟩,
  ⟨.sphere, .equation, 2, 19, 144, [2], 21, 145, [1]⟩,
  ⟨.sphere, .equation, 2, 19, 144, [1], 21, 145, [0]⟩,
  ⟨.sphere, .equation, 3, 20, 145, [0], 23, 147, [2]⟩,
  ⟨.sphere, .equation, 2, 20, 145, [2], 22, 146, [3]⟩,
  ⟨.sphere, .equation, 2, 21, 146, [2], 23, 147, [3]⟩,
  ⟨.sphere, .equation, 2, 21, 146, [1], 23, 147, [1, 2]⟩,
  ⟨.sphere, .equation, 4, 21, 147, [1], 25, 150, [3]⟩,
  ⟨.sphere, .reaches, 4, 21, 147, [0], 21, 147, []⟩,
  ⟨.sphere, .equation, 4, 18, 144, [1], 22, 147, [1]⟩,
  ⟨.sphere, .equation, 4, 18, 144, [2, 3], 22, 147, [0, 3]⟩,
  ⟨.sphere, .equation, 2, 22, 147, [3], 24, 148, [1]⟩,
  ⟨.sphere, .equation, 2, 22, 147, [2], 24, 148, [0]⟩,
  ⟨.sphere, .equation, 3, 23, 148, [0], 26, 150, [2]⟩,
  ⟨.sphere, .equation, 2, 23, 148, [1], 25, 149, [2]⟩,
  ⟨.sphere, .equation, 2, 24, 149, [0], 26, 150, [1]⟩,
  ⟨.sphere, .reaches, 1000, 25, 150, [2], 25, 150, []⟩,
  ⟨.sphere, .reaches, 1000, 25, 150, [0, 1], 25, 150, []⟩,
  ⟨.sphere, .equation, 2, 25, 150, [1], 27, 151, [0]⟩,
  ⟨.sphere, .equation, 2, 26, 151, [0], 28, 152, [1]⟩,
  ⟨.sphere, .equation, 2, 26, 152, [0], 28, 153, [2]⟩,
  ⟨.sphere, .equation, 2, 26, 152, [1], 28, 153, [1]⟩,
  ⟨.sphere, .equation, 2, 27, 152, [1], 29, 153, [2]⟩,
  ⟨.sphere, .equation, 2, 27, 152, [0], 29, 153, [0]⟩,
  ⟨.sphere, .equation, 2, 27, 153, [0], 29, 154, [0]⟩,
  ⟨.sphere, .equation, 2, 28, 153, [3], 30, 154, [1]⟩,
  ⟨.sphere, .equation, 2, 28, 153, [0], 30, 154, [0]⟩,
  ⟨.sphere, .equation, 2, 28, 154, [0], 30, 155, [1]⟩,
  ⟨.sphere, .equation, 3, 29, 154, [1], 32, 156, [0]⟩,
  ⟨.sphere, .equation, 2, 29, 155, [0], 31, 156, [1]⟩,
  ⟨.sphere, .equation, 2, 29, 155, [1], 31, 156, [2]⟩,
  ⟨.sphere, .equation, 2, 30, 155, [0], 32, 156, [1]⟩,
  ⟨.sphere, .equation, 4, 31, 156, [0], 35, 159, [0]⟩,
  ⟨.sphere, .equation, 3, 31, 157, [0], 34, 159, [0]⟩,
  ⟨.sphere, .equation, 2, 32, 158, [0], 34, 159, [1]⟩,
  ⟨.sphere, .equation, 2, 33, 158, [0], 35, 159, [1]⟩,
  ⟨.sphere, .equation, 3, 33, 159, [0], 36, 161, [1]⟩,
  ⟨.sphere, .equation, 2, 35, 161, [0], 37, 162, [1]⟩,
  ⟨.sphere, .equation, 2, 36, 161, [0], 38, 162, [1]⟩,
  ⟨.sphere, .equation, 2, 37, 162, [0], 39, 163, [0]⟩,
  ⟨.sphere, .equation, 3, 38, 163, [0], 41, 165, [1, 2]⟩,
  ⟨.sphere, .equation, 2, 38, 164, [0], 40, 165, [1]⟩,
  ⟨.sphere, .equation, 4, 39, 164, [0], 43, 167, [0]⟩,
  ⟨.sphere, .equation, 2, 40, 165, [0], 42, 166, [1]⟩,
  ⟨.sphere, .equation, 3, 41, 166, [0], 44, 168, [0]⟩,
  ⟨.sphere, .equation, 2, 41, 166, [1], 43, 167, [1]⟩,
  ⟨.sphere, .equation, 2, 42, 167, [0], 44, 168, [1]⟩,
  ⟨.sphere, .equation, 4, 42, 168, [2], 46, 171, [0]⟩,
  ⟨.sphere, .equation, 3, 42, 168, [0], 45, 170, [0]⟩,
  ⟨.sphere, .equation, 4, 43, 168, [0], 47, 171, [0]⟩,
  ⟨.sphere, .equation, 2, 43, 168, [1], 45, 169, [0]⟩,
  ⟨.sphere, .equation, 2, 44, 169, [0], 46, 170, [0]⟩,
  ⟨.sphere, .equation, 4, 45, 171, [0], 49, 174, [0]⟩,
  ⟨.sphere, .equation, 4, 52, 177, [0], 56, 180, [0]⟩,
  ⟨.sphere, .equation, 3, 54, 180, [0], 57, 182, [0]⟩,
  ⟨.sphere, .equation, 2, 55, 180, [0], 57, 181, [0]⟩,
  ⟨.sphere, .equation, 2, 56, 181, [0], 58, 182, [0]⟩,
  ⟨.sphere, .refutation, 3, 6, 132, [0], 9, 134, []⟩,
  ⟨.sphere, .refutation, 3, 6, 132, [0], 9, 134, [2]⟩,
  ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, []⟩,
  ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [3]⟩,
  ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [2]⟩,
  ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [2, 3]⟩,
  ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [0, 1]⟩,
  ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [0, 1, 3]⟩,
  ⟨.moore, .equation, 4, 8, 132, [0], 12, 135, []⟩,
  ⟨.sphere, .equation, 7, 9, 132, [0, 1], 16, 138, []⟩
]

end KIP126.SSComputation.Input

namespace KIP126.Computation.Table.Raw

/-- The sphere/Cν projection of the unified input table, preserving row order. -/
public def claims : List Claim :=
  KIP126.SSComputation.Input.claims.filterMap KIP126.SSComputation.Input.Claim.toRaw?

end KIP126.Computation.Table.Raw
