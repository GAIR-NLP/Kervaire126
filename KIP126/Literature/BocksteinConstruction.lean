module

public import KIP126.Literature.SyntheticComparison

/-! Finite obstruction theory for the lambda quotient tower,
using its specified restriction and connecting maps.
-/

@[expose] section
namespace KIP126.Literature.BocksteinConstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : AdamsSyntheticBackground C Syn)

private theorem regrade_eq_zero_iff {m m' w w' : ℤ} {Y : Syn}
    (hm : m = m') (hw : w = w') (a : BiHom m w Y) :
    homotopyRegrade hm hw a = 0 ↔ a = 0 := by
  subst m'
  subst w'
  rfl

include D in
private theorem suspension_zero (m n k l : ℤ) (Y : Syn) :
    susp_invariance m n k l Y 0 = 0 := by
  letI := D.exactness.shiftAdditive (k,l)
  simp only [susp_invariance, Equiv.trans_apply,
    Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply,
    Functor.map_zero, comp_zero, zero_comp]

include D in
private theorem suspension_symm_eq_zero_iff (m n k l : ℤ) (Y : Syn)
    (a : BiHom (m+k) (n+l) ((SyntheticCategory.biShift (k,l)).obj Y)) :
    (susp_invariance m n k l Y).symm a = 0 ↔ a = 0 := by
  rw [Equiv.symm_apply_eq]
  rw [suspension_zero D]

private theorem postcompose_iso_zero_iff {A B E : Syn}
    (a : A ⟶ B) (e : B ⟶ E) [IsIso e] : a ≫ e = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (cancel_mono e).mp
    simpa only [zero_comp] using h
  · rintro rfl
    exact zero_comp

/-- The displayed E₂ label vanishes exactly when the actual connecting
arrow vanishes; regrading and the first-quotient coordinates are invertible. -/
theorem label_zero_iff_boundary_zero (X : AdamsObject (coefficients := D.coefficients)) (q : ℕ)
    (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (nuZero D X) q)) :
    bocksteinLabel D X q hq s t a = 0 ↔
      a ≫ ((D.quotients.tower (nuZero D X)).triangle hq
        (Nat.lt_succ_self q)).delta = 0 := by
  unfold bocksteinLabel
  rw [LinearEquiv.map_eq_zero_iff, regrade_eq_zero_iff,
    suspension_symm_eq_zero_iff D, regrade_eq_zero_iff]
  unfold bocksteinArrow
  simp only [← Category.assoc, postcompose_iso_zero_iff]

/-- A class in the q-th quotient has zero actual Bockstein obstruction
exactly when it extends along the specified restriction from quotient q+1. -/
theorem label_zero_iff_lift (X : AdamsObject (coefficients := D.coefficients)) (q : ℕ)
    (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (nuZero D X) q)) :
    bocksteinLabel D X q hq s t a = 0 ↔
      ∃ b : BiHom (t-s) t (XModLambdaN (nuZero D X) (q+1)),
        b ≫ (D.quotients.tower (nuZero D X)).rho q (q+1)
          (Nat.le_succ q) = a := by
  rw [label_zero_iff_boundary_zero D]
  let Q := D.quotients.tower (nuZero D X)
  let T := Q.triangle hq (Nat.lt_succ_self q)
  constructor
  · intro h
    obtain ⟨b,hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₃
      T.distinguished a h
    refine ⟨b, ?_⟩
    rw [← Q.triangle_rho hq (Nat.lt_succ_self q)]
    exact hb.symm
  · rintro ⟨b,rfl⟩
    rw [← Q.triangle_rho hq (Nat.lt_succ_self q)]
    rw [Category.assoc]
    have h := comp_distTriang_mor_zero₂₃
      (Triangle.mk T.lambdaMap T.rho T.delta) T.distinguished
    change T.rho ≫ T.delta = 0 at h
    rw [h, comp_zero]

/-- A lift to a later quotient restricts to a lift to every earlier
positive quotient, with the original first-quotient label unchanged. -/
theorem restrict_lift (X : AdamsObject (coefficients := D.coefficients)) (i j : ℕ) (hi : 0 < i)
    (hij : i ≤ j) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (XModLambdaN (nuZero D X) j))
    (ha : a ≫ (D.quotients.tower (nuZero D X)).rho 1 j (by omega) =
      firstLabel D X s t x) :
    (a ≫ (D.quotients.tower (nuZero D X)).rho i j hij) ≫
        (D.quotients.tower (nuZero D X)).rho 1 i hi = firstLabel D X s t x := by
  rw [Category.assoc, FiniteLambdaQuotientTower.rho_comp]
  exact ha

/-- At quotient length one the lifting criterion is the identity map,
matching the fact that every E₂ label reaches E₂, including zero. -/
theorem finite_lift_one (X : AdamsObject (coefficients := D.coefficients)) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    ReachesPage (D.classical.obj (X.obj D.auxiliary)) 2 (s,t) x ↔
      ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) 1),
        a ≫ (D.quotients.tower (nuZero D X)).rho 1 1 le_rfl =
          firstLabel D X s t x := by
  constructor
  · intro _
    exact ⟨firstLabel D X s t x, by
      rw [FiniteLambdaQuotientTower.rho_id, Category.comp_id]⟩
  · intro _
    exact ⟨x, RepresentsOnPage.self_two x⟩

end
end KIP126.Literature.BocksteinConstruction
