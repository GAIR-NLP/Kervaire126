module
import all KIP126.AdamsComputation.Table.Internal.ZeroDimension

public import KIP126.AdamsComputation.Table
public import KIP126.AdamsComputation.Table.ValueData
import all KIP126.AdamsComputation.Table.ValueSyntax
import all KIP126.AdamsComputation.Table.Internal.SphereValueChecks
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Monomial-to-coordinate bindings for the sphere Adams E₂ algebra. -/
@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.AdamsSynthetic.Completed
noncomputable section

public def Expression.degree : Expression → ℕ × ℕ
  | .one => (0,0)
  | .named a => a.degree
  | .generator _ s t => (s,t)
  | .mul a b => (a.degree.1+b.degree.1,a.degree.2+b.degree.2)

public def generatorImage (id s t : ℕ) : Page .sphere s t :=
  if ht : t ≤ 261 then
    if hi : id < Standard.archive.generators.count then
      if hd : Standard.archive.generators.degree ⟨id,hi⟩ = (s,t) then
        Standard.comparison s t ht
          ((eqToHom (congrArg (fun p : ℕ × ℕ => Standard.sourceData.component p.1 p.2) hd))
            (Standard.sourceGenerator ⟨id,hi⟩))
      else 0
    else 0
  else 0

public def Expression.value : (e : Expression) → Page .sphere e.degree.1 e.degree.2
  | .one => background.sphereAlgebra.unit
  | .named a => Standard.atom a
  | .generator id s t => generatorImage id s t
  | .mul a b => Standard.product a.value b.value
      (by simp only [Expression.degree, Prod.mk_add_mk, Nat.cast_add])

/- Normalize archived monomials and displayed expressions in sphere E₂
using the multiplication's HEq laws and the total-degree monoid. -/
section ArchiveBasisValueConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed

private abbrev ActualTotal := Σ p : Bidegree, background.classical.sphere.Page 2 p
private noncomputable def totalProduct (x y : ActualTotal) : ActualTotal :=
  ⟨x.1+y.1, background.sphereAlgebra.product x.1 y.1 x.2 y.2⟩
private noncomputable def totalUnit : ActualTotal := ⟨(0,0), background.sphereAlgebra.unit⟩
private theorem totalProduct_assoc (x y z : ActualTotal) :
    totalProduct (totalProduct x y) z = totalProduct x (totalProduct y z) := by
  apply Sigma.ext (add_assoc x.1 y.1 z.1)
  exact background.sphereAlgebra.assoc x.1 y.1 z.1 x.2 y.2 z.2
private theorem totalUnit_left (x : ActualTotal) : totalProduct totalUnit x = x := by
  apply Sigma.ext (zero_add x.1)
  exact background.sphereAlgebra.unit_left x.1 x.2
private theorem totalUnit_right (x : ActualTotal) : totalProduct x totalUnit = x := by
  apply Sigma.ext (add_zero x.1)
  exact background.sphereAlgebra.unit_right x.1 x.2
private noncomputable instance actualTotalMonoid : Monoid ActualTotal where
  mul := totalProduct
  one := totalUnit
  mul_assoc := totalProduct_assoc
  one_mul := totalUnit_left
  mul_one := totalUnit_right

private noncomputable def totalClass {s t : ℕ} (x : Page .sphere s t) : ActualTotal :=
  ⟨(s,t), x⟩
private theorem totalClass_product {s t s' t' : ℕ}
    (x : Page .sphere s t) (y : Page .sphere s' t') :
    totalClass (Standard.product (r := ((s+s' : ℕ),(t+t' : ℕ))) x y
      (by simp only [Prod.mk_add_mk,Nat.cast_add])) = totalClass x * totalClass y := by
  rfl

private noncomputable def totalGenerator (id : ℕ) : ActualTotal :=
  if hi : id < Standard.archive.generators.count then
    let d := Standard.archive.generators.degree ⟨id,hi⟩
    totalClass (generatorImage id d.1 d.2)
  else totalClass (0 : Page .sphere 0 0)

private noncomputable def actualMonomial {s t : ℕ}
    (m : SourceMonomial Standard.archive.generators s t) (ht : t ≤ 261) : ActualTotal :=
  totalClass (Standard.comparison s t ht (m.value Standard.sourceData Standard.sourceGenerator))

private theorem actualMonomial_product {s t s' t' : ℕ}
    (a : SourceMonomial Standard.archive.generators s t)
    (b : SourceMonomial Standard.archive.generators s' t')
    (ht : t+t' ≤ 261) (ha : t ≤ 261) (hb : t' ≤ 261) :
    actualMonomial (.mul a b) ht = actualMonomial a ha * actualMonomial b hb := by
  refine Sigma.ext ?_ ?_
  · rfl
  exact heq_of_eq (Standard.comparison_product s t s' t' ht
    (a.value Standard.sourceData Standard.sourceGenerator)
    (b.value Standard.sourceData Standard.sourceGenerator))

private theorem actualMonomial_normalize {s t : ℕ}
    (m : SourceMonomial Standard.archive.generators s t) :
    ∀ ht : t ≤ 261, actualMonomial m ht = (monomialWord m |>.map totalGenerator).prod := by
  induction m with
  | one =>
    intro ht
    exact congrArg (fun x : Page .sphere 0 0 => totalClass x) Standard.comparison_unit
  | generator i =>
    intro ht
    simp only [monomialWord, List.map_singleton, List.prod_singleton]
    dsimp only [actualMonomial, SourceMonomial.value, totalGenerator]
    rw [dif_pos i.isLt]
    dsimp only [generatorImage]
    rw [dif_pos ht, dif_pos i.isLt, dif_pos rfl]
    rfl
  | @mul s t s' t' a b iha ihb =>
    intro ht
    have ha : t ≤ 261 := by omega
    have hb : t' ≤ 261 := by omega
    rw [actualMonomial_product a b ht ha hb, iha ha, ihb hb]
    simp only [monomialWord, List.map_append, List.prod_append]

private theorem named_total (a : Atom) :
    totalClass (Standard.atom a) = totalGenerator (Standard.archive.atomIndex a).val := by
  cases a <;> rfl

private theorem expression_normalize (e : Expression) (hv : admissible e) :
    totalClass e.value = (expressionWord e |>.map totalGenerator).prod := by
  induction e with
  | one => rfl
  | named a =>
    dsimp only [Expression.value]
    simpa only [expressionWord, List.map_singleton, List.prod_singleton] using named_total a
  | generator id s t =>
    dsimp only [admissible] at hv
    split_ifs at hv with hi
    · have hs := congrArg Prod.fst hv
      have ht := congrArg Prod.snd hv
      dsimp only at hs ht
      subst s
      subst t
      simp only [expressionWord, List.map_singleton, List.prod_singleton]
      dsimp only [totalGenerator]
      rw [dif_pos hi]
      rfl
  | mul a b iha ihb =>
    rw [show totalClass (Expression.mul a b).value = totalClass a.value * totalClass b.value from rfl]
    rw [iha hv.1, ihb hv.2]
    simp only [expressionWord, List.map_append, List.prod_append]


private theorem expressionDegree_agrees (e : Expression) :
    expressionDegree e = e.degree := by
  induction e with
  | one => rfl
  | named a => rfl
  | generator id s t => rfl
  | mul a b iha ihb =>
    simp only [expressionDegree, Expression.degree, iha, ihb]

private theorem row_binding (v : BasisValue) (hrow : rowValid v) :
    basis .sphere v.expression.degree.1 v.expression.degree.2 v.index = v.expression.value := by
  have hrow' : admissible v.expression ∧ v.expression.degree.2 ≤ 261 ∧
      checkedWord v.expression.degree.1 v.expression.degree.2 v.index =
        some (expressionWord v.expression) := by
    simpa only [rowValid, expressionDegree_agrees] using hrow
  have hword := hrow'.2.2
  dsimp only [checkedWord] at hword
  split_ifs at hword with hi
  have hw := Option.some.inj hword
  let m := Standard.archive.basisMonomial v.expression.degree.1 v.expression.degree.2 ⟨v.index,hi⟩
  have hm := actualMonomial_normalize m hrow'.2.1
  have he := expression_normalize v.expression hrow'.1
  change monomialWord m = expressionWord v.expression at hw
  rw [hw] at hm
  have htotal := hm.trans he.symm
  dsimp only [actualMonomial, totalClass] at htotal
  have hactual := sigma_mk_injective htotal
  have hb := Standard.coordinates_basis v.expression.degree.1 v.expression.degree.2 hrow'.2.1
    (⟨v.index,hi⟩ : Fin (Standard.archive.basisCount v.expression.degree.1 v.expression.degree.2))
  dsimp only [basis, sphereBasis]
  rw [dif_pos hrow'.2.1, dif_pos hi]
  exact hb.trans hactual


private theorem archiveBasisValueBinding (v : BasisValue) (hv : v ∈ basisValues) :
    basis .sphere v.expression.degree.1 v.expression.degree.2 v.index = v.expression.value := by
  apply row_binding v
  exact of_decide_eq_true ((List.all_eq_true.mp basisValues_checked) v hv)

end ArchiveBasisValueConstruction

/-- Archived monomials equal their sphere E₂ coordinate vectors. -/
public theorem basis_value (v : BasisValue) (hv : v ∈ basisValues) :
    basis .sphere v.expression.degree.1 v.expression.degree.2 v.index =
      v.expression.value := by
  exact archiveBasisValueBinding v hv

public theorem basis_P : basis .sphere 11 133 1 = Standard.P := by
  have h := basis_value ⟨.mul (.named .h6) (.named .M_mul_d_0),1⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.P, Standard.atom_h6] using h

public theorem basis_Q : basis .sphere 12 134 0 = Standard.Q := by
  have h := basis_value ⟨.mul (.named .h5) (.named .x_91_11),0⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.Q, Standard.atom_h5] using h

public theorem basis_T : basis .sphere 14 139 1 = Standard.T := by
  have h := basis_value ⟨.mul (.named .h1) (.mul (.named .h4) (.named .x_109_12)),1⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.T, Standard.atom_h1,
    Standard.atom_h4] using h

/-- The first sphere relation, `0,1,1,1`, transported to the same actual E₂. -/
public theorem h0_h1_zero :
    Standard.product (r := (2,3)) Standard.h0 Standard.h1 = 0 := by
  exact Internal.actual_page_zero 2 3 (by decide) (by decide) _

public theorem basis_correction : basis .sphere 13 137 1 = Standard.correction := by
  have h := basis_value ⟨.mul (.named .e0) (.named .delta_h_6_mul_g),1⟩ (by decide)
  exact h

public theorem basis_h4_x109 : basis .sphere 13 137 2 =
    Standard.product (r := (13,137)) Standard.h4 (Standard.atom .x_109_12) := by
  have h := basis_value ⟨.mul (.named .h4) (.named .x_109_12),2⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.atom_h4] using h

public theorem basis_U : basis .sphere 10 134 4 = Standard.U := by
  have h := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.named .x_124_8),4⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.U, Standard.h0Square,
    Standard.atom_h0] using h

/- Commutativity transported from the native quotient through the bounded
comparison, with the two degree casts. -/
section NativeSourceCommutativity
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem comparison_heq {s t u v : ℕ} (hs : s = u) (ht : t = v)
    (ha : t ≤ 261) (hb : v ≤ 261)
    (x : Standard.sourceData.component s t) (y : Standard.sourceData.component u v)
    (hxy : HEq x y) :
    HEq (Standard.comparison s t ha x) (Standard.comparison u v hb y) := by
  subst u
  subst v
  cases hxy
  rfl

private theorem transport_heq {X Y : ModuleCat.{0} ℤ} (h : X = Y) (x : X) :
    HEq ((eqToHom h) x) x := by
  cases h
  rfl

private theorem product_transport_heq {p q r : ℤ × ℤ}
    (x : background.classical.sphere.Page 2 p) (y : background.classical.sphere.Page 2 q)
    (h : p + q = r) :
    HEq (Standard.product (r := r) x y h) (background.sphereAlgebra.product p q x y) := by
  exact transport_heq (congrArg (background.classical.sphere.Page 2) h) _

private theorem native_source_product_comm (s t s' t' : ℕ)
    (a : Standard.sourceData.component s t) (b : Standard.sourceData.component s' t') :
    HEq (Standard.sourceData.product s t s' t' a b)
      (Standard.sourceData.product s' t' s t b a) := by
  apply (Subtype.heq_iff_coe_eq (by
    intro z
    rw [Nat.add_comm s s', Nat.add_comm t t'])).2
  exact mul_comm _ _

private theorem actual_product_comm (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t')) :
    HEq (background.sphereAlgebra.product (s,t) (s',t') x y)
      (background.sphereAlgebra.product (s',t') (s,t) y x) := by
  let a := (Standard.comparison s t (by omega)).symm x
  let b := (Standard.comparison s' t' (by omega)).symm y
  have ha : Standard.comparison s t (by omega) a = x :=
    (Standard.comparison s t (by omega)).apply_symm_apply x
  have hb : Standard.comparison s' t' (by omega) b = y :=
    (Standard.comparison s' t' (by omega)).apply_symm_apply y
  have hsource := native_source_product_comm s t s' t' a b
  have hactual := comparison_heq (Nat.add_comm s s') (Nat.add_comm t t')
    ht (by omega) _ _ hsource
  rw [Standard.comparison_product, Standard.comparison_product, ha, hb] at hactual
  exact hactual

end NativeSourceCommutativity

/-- Commutativity of sphere E₂ multiplication within the total-degree bound
of comparison_product. -/
public theorem product_comm (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t')) :
    Standard.product (r := ((s+s' : ℕ),(t+t' : ℕ))) x y
        (by simp only [Prod.mk_add_mk,Nat.cast_add]) =
      Standard.product (r := ((s+s' : ℕ),(t+t' : ℕ))) y x
        (by simp only [Prod.mk_add_mk,Nat.cast_add]; ext <;> omega) := by
  exact eq_of_heq ((product_transport_heq x y _).trans
    ((actual_product_comm s t s' t' ht x y).trans (product_transport_heq y x _).symm))

end
end KIP126.Computation.Table
