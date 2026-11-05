module

public import KIP126.AdamsSynthetic

/-! Algebra, basis and Adams E₂ comparison for the Lin sphere calculation.
Computation.Standard supplies the untruncated quotient. -/

@[expose] section
namespace KIP126.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams
universe u v w
public inductive Atom
  | h0 | h1 | h6 | h2 | h4 | h5 | h3 | h7 | g | e0 | delta_h_1_mul_g | delta_h_6_mul_g | M_mul_d_0 | b4 | b
  | x_91_11 | x_94_8 | x_109_12 | x_121_7 | x_125_5 | x_126_4
  | x_123_8 | x_123_9 | x_124_8 | x_126_6 | x_125_8
  | x_123_11 | x_123_11_2 | x_125_9_2 | x_126_8 | x_126_8_2 | x_126_8_4
  | x_123_13_2 | x_122_15_2 | x_121_17 | x_122_16
  deriving DecidableEq, Repr

/-- Local generator index, mathematical name and bidegree `(s,t)`. -/
public abbrev Atom.record : Atom → Nat × String × Nat × Nat
  | .h0 => (0, "h_0", 1, 1)
  | .h1 => (1, "h_1", 1, 2)
  | .h6 => (69, "h_6", 1, 64)
  | .h2 => (2, "h_2", 1, 4)
  | .h4 => (7, "h_4", 1, 16)
  | .h5 => (18, "h_5", 1, 32)
  | .h3 => (3, "h_3", 1, 8)
  | .h7 => (324, "h_7", 1, 128)
  | .g => (13, "g", 4, 24)
  | .e0 => (9, "e_0", 4, 21)
  | .delta_h_1_mul_g => (51, "\\Delta h_1g", 9, 54)
  | .delta_h_6_mul_g => (251, "\\Delta h_6g", 9, 116)
  | .M_mul_d_0 => (79, "Md_0", 10, 69)
  | .b4 => (80, "[B_4]", 9, 69)
  | .b => (82, "(\\Delta e_1+C_0+h_0^6h_5^2)", 8, 70)
  | .x_91_11 => (188, "x_{91,11}", 11, 102)
  | .x_94_8 => (190, "x_{94,8}", 8, 102)
  | .x_109_12 => (275, "x_{109,12}", 12, 121)
  | .x_121_7 => (323, "x_{121,7}", 7, 128)
  | .x_125_5 => (340, "x_{125,5}", 5, 130)
  | .x_126_4 => (341, "x_{126,4}", 4, 130)
  | .x_123_8 => (352, "x_{123,8}", 8, 131)
  | .x_123_9 => (366, "x_{123,9}", 9, 132)
  | .x_124_8 => (367, "x_{124,8}", 8, 132)
  | .x_126_6 => (368, "x_{126,6}", 6, 132)
  | .x_125_8 => (375, "x_{125,8}", 8, 133)
  | .x_123_11 => (386, "x_{123,11}", 11, 134)
  | .x_123_11_2 => (387, "x_{123,11,2}", 11, 134)
  | .x_125_9_2 => (391, "x_{125,9,2}", 9, 134)
  | .x_126_8 => (392, "x_{126,8}", 8, 134)
  | .x_126_8_2 => (393, "x_{126,8,2}", 8, 134)
  | .x_126_8_4 => (395, "x_{126,8,4}", 8, 134)
  | .x_123_13_2 => (418, "x_{123,13,2}", 13, 136)
  | .x_122_15_2 => (424, "x_{122,15,2}", 15, 137)
  | .x_121_17 => (436, "x_{121,17}", 17, 138)
  | .x_122_16 => (437, "x_{122,16}", 16, 138)


/-- Bidegree of a source label. -/
public abbrev Atom.degree (a : Atom) : ℕ × ℕ := (a.record.2.2.1, a.record.2.2.2)

/-- The eight named generators of the finite one-line input. -/
public def Atom.ofHi : KIP126.AdamsSynthetic.SphereData.Index → Atom
  | ⟨0, _⟩ => .h0
  | ⟨1, _⟩ => .h1
  | ⟨2, _⟩ => .h2
  | ⟨3, _⟩ => .h3
  | ⟨4, _⟩ => .h4
  | ⟨5, _⟩ => .h5
  | ⟨6, _⟩ => .h6
  | ⟨7, _⟩ => .h7

public theorem Atom.ofHi_record : ∀ i : KIP126.AdamsSynthetic.SphereData.Index,
    (Atom.ofHi i).record = KIP126.AdamsSynthetic.SphereData.record i := by decide

public theorem Atom.ofHi_degree : ∀ i : KIP126.AdamsSynthetic.SphereData.Index,
    (Atom.ofHi i).degree = (1, 2 ^ i.val) := by decide

/-- A graded source algebra with homogeneous components, product, unit and
generators indexed by `Atom.record`. Computation.Standard supplies the
untruncated quotient of the archived polynomial algebra. -/
public structure ProgramData where
  component : ℕ → ℕ → ModuleCat.{v} (ZMod 2)
  product : ∀ s t s' t', component s t →ₗ[ZMod 2]
    component s' t' →ₗ[ZMod 2] component (s+s') (t+t')
  unit : component 0 0
  atom : ∀ a : Atom, component a.degree.1 a.degree.2

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Comparison of the source algebra with sphere Adams E₂ through t = 261.
Product compatibility is bounded by the total internal degree. -/
public structure SpherePresentation (D : AdamsSyntheticBackground C Syn) (P : ProgramData.{v}) where
  comparison : ∀ s t : ℕ, t ≤ 261 →
    P.component s t ≃ₗ[ℤ] D.classical.sphere.Page 2 ((s : ℤ),(t : ℤ))
  comparison_product : ∀ s t s' t' : ℕ, ∀ h : t+t' ≤ 261,
    ∀ (x : P.component s t) (y : P.component s' t'),
    comparison (s+s') (t+t') h (P.product s t s' t' x y) =
      D.sphereAlgebra.product (s,t) (s',t')
        (comparison s t (by omega) x) (comparison s' t' (by omega) y)
  comparison_unit : comparison 0 0 (by decide) P.unit = D.sphereAlgebra.unit
  h0 : comparison 1 1 (by decide) (P.atom .h0) = D.standardClasses.standardHi 0
  h1 : comparison 1 2 (by decide) (P.atom .h1) = D.standardClasses.standardHi 1
  h2 : comparison 1 4 (by decide) (P.atom .h2) = D.standardClasses.standardHi 2
  h4 : comparison 1 16 (by decide) (P.atom .h4) = D.standardClasses.standardHi 4
  h5 : comparison 1 32 (by decide) (P.atom .h5) = D.standardClasses.standardHi 5
  h6 : comparison 1 64 (by decide) (P.atom .h6) = D.standardClasses.standardH6

namespace SpherePresentation
variable {D : AdamsSyntheticBackground C Syn} {P : ProgramData.{v}}

/-- F₂-linear comparison induced by the additive comparison. -/
public noncomputable def comparisonF2 (e : SpherePresentation D P) (s t : ℕ)
    (ht : t ≤ 261) :
    letI := D.sphereAlgebra.scalar (s,t)
    P.component s t ≃ₗ[ZMod 2] D.classical.sphere.Page 2 (s,t) := by
  letI := D.sphereAlgebra.scalar (s,t)
  exact { (e.comparison s t ht).toAddEquiv with
    map_smul' := fun a x => ZMod.map_smul (e.comparison s t ht).toAddMonoidHom a x }

public theorem comparison_mul (e : SpherePresentation D P) (s t s' t' : ℕ)
    (h : t+t' ≤ 261) (x : P.component s t) (y : P.component s' t') :
    e.comparison (s+s') (t+t') h (P.product s t s' t' x y) =
      D.sphereAlgebra.product (s,t) (s',t')
        (e.comparison s t (by omega) x) (e.comparison s' t' (by omega) y) :=
  e.comparison_product s t s' t' h x y

/-- The data square becomes the actual product of the designated h₆. -/
public theorem h6_square (e : SpherePresentation D P) :
    e.comparison 2 128 (by decide)
      (P.product 1 64 1 64 (P.atom .h6) (P.atom .h6)) =
      D.standardClasses.standardH6Square := by
  have h := e.comparison_mul 1 64 1 64 (by decide) (P.atom .h6) (P.atom .h6)
  change e.comparison 2 128 _ (P.product 1 64 1 64 (P.atom .h6) (P.atom .h6)) =
    D.sphereAlgebra.product (1,64) (1,64)
      (e.comparison 1 64 _ (P.atom .h6)) (e.comparison 1 64 _ (P.atom .h6)) at h
  rw [e.h6] at h
  exact h

end SpherePresentation
end KIP126.Computation
