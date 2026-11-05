module
public import KIP126.Literature.Standard
public import KIP126.AdamsSynthetic.SphereTensor
public import Mathlib.CategoryTheory.Monoidal.Mon
/-! Quotient algebras and their sphere-action comparisons in the fixed model. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.Synthetic.Context
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.privateInPublic true

public def quotientAlgebraProduct {A : SyntheticSpectrum} (Q : MonObj A) {m n k l : ℤ}
    (x : BiHom m n A) (y : BiHom k l A) : BiHom (m+k) (n+l) A :=
  (SyntheticCategory.biShift_comp (m,n) (k,l)).inv.app S_0_0 ≫
    (biShift_eq_tensor_Smn k l (Smn m n)).hom ≫ (y ⊗ₘ x) ≫ Q.mul

private structure QuotientAlgebraConstructionData where
  quotientSyntheticSymmetric : SymmetricCategory SyntheticSpectrum
  quotientAlgebra (q : ℕ) (hq : 0<q) :
      MonObj (XModLambdaN (S_0_0 : SyntheticSpectrum) q)
  quotientAlgebra_commutative (q : ℕ) (hq : 0<q) :
      letI := quotientSyntheticSymmetric
      letI := quotientAlgebra q hq
      IsCommMonObj (XModLambdaN (S_0_0 : SyntheticSpectrum) q)
  quotientAlgebra_unit (q : ℕ) (hq : 0<q) :
      (quotientAlgebra q hq).one=XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q
  quotientAlgebra_sphere_action (q : ℕ) (hq : 0<q) (m n k l : ℤ)
      (x : BiHom m n (S_0_0 : SyntheticSpectrum))
      (y : BiHom k l (XModLambdaN (S_0_0 : SyntheticSpectrum) q)) :
      quotientAlgebraProduct (quotientAlgebra q hq) (quotientClass q x) y=sphereAction x y

private def quotientAlgebraConstruction : QuotientAlgebraConstructionData where
  quotientSyntheticSymmetric := by sorry
  quotientAlgebra := by sorry
  quotientAlgebra_commutative := by sorry
  quotientAlgebra_unit := by sorry
  quotientAlgebra_sphere_action := by sorry

@[implicit_reducible] public def quotientSyntheticSymmetric : SymmetricCategory SyntheticSpectrum :=
  quotientAlgebraConstruction.quotientSyntheticSymmetric
@[implicit_reducible] public def quotientAlgebra (q : ℕ) (hq : 0<q) :
    MonObj (XModLambdaN (S_0_0 : SyntheticSpectrum) q) :=
  quotientAlgebraConstruction.quotientAlgebra q hq
public theorem quotientAlgebra_commutative (q : ℕ) (hq : 0<q) :
    letI := quotientSyntheticSymmetric
    letI := quotientAlgebra q hq
    IsCommMonObj (XModLambdaN (S_0_0 : SyntheticSpectrum) q) := by
  exact quotientAlgebraConstruction.quotientAlgebra_commutative q hq
public theorem quotientAlgebra_unit (q : ℕ) (hq : 0<q) :
    (quotientAlgebra q hq).one=XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q := by
  exact quotientAlgebraConstruction.quotientAlgebra_unit q hq
public theorem quotientAlgebra_sphere_action (q : ℕ) (hq : 0<q) (m n k l : ℤ)
    (x : BiHom m n (S_0_0 : SyntheticSpectrum))
    (y : BiHom k l (XModLambdaN (S_0_0 : SyntheticSpectrum) q)) :
    quotientAlgebraProduct (quotientAlgebra q hq) (quotientClass q x) y=sphereAction x y := by
  exact quotientAlgebraConstruction.quotientAlgebra_sphere_action q hq m n k l x y

/-- The first-quotient product comparison for arbitrary classes in the same
selected first-quotient algebra. -/


public theorem quotientAlgebra_first_quotient (s t s' t' : ℕ)
    (x : BiHom ((t : ℤ)-s) t (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))
    (y : BiHom ((t' : ℤ)-s') t' (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient background ((s+s' : ℕ) : ℤ) ((t+t' : ℕ) : ℤ)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]) (quotientAlgebraProduct (quotientAlgebra 1 (by decide)) x y)) =
      (eqToHom (congrArg (background.classical.sphere.Page 2)
        (show ((s : ℤ),(t : ℤ)) + ((s' : ℤ),(t' : ℤ)) = (((s+s' : ℕ) : ℤ),((t+t' : ℕ) : ℤ)) by
          simp only [Prod.mk_add_mk,Nat.cast_add])))
        (background.sphereAlgebra.product (s,t) (s',t')
          (KIP126.Literature.sphereFirstQuotient background s t x)
          (KIP126.Literature.sphereFirstQuotient background s' t' y)) := by
  sorry

end
end KIP126.Literature.Standard
