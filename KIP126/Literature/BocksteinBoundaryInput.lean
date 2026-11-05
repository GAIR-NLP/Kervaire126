module

import all KIP126.Literature.BocksteinComparisonInput

/-! Geometric boundary labels for the fixed lambda tower, quotient
restriction, triangle boundary and suspension normalization. -/






@[expose] section
namespace KIP126.Literature.Paper38BoundaryInput
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Literature.Paper38ComparisonInput
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Local rewrites in the fixed BHS coordinates avoid global simp
congruence declarations. -/
private noncomputable def biSuspensionIso (q : ℤ) (Q : SyntheticSpectrum) :
    (SyntheticCategory.biShift (1, -q)).obj Q ≅
      ((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧ := by
  have h : ((0 : ℤ), -q) + (1, 0) = (1, -q) := by
    ext <;> simp
  simpa only [h] using
    ((SyntheticCategory.biShift_comp (0, -q) (1, 0)).symm.app Q ≪≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).app
        ((SyntheticCategory.biShift (0, -q)).obj Q))

/-- The underlying equivalence for the Bockstein landing degree. It is the
inverse of the existing suspension invariance, followed by the specified
ordinary-suspension comparison and the integer degree equalities. -/
private noncomputable def biSuspensionHomEquivRaw (n w q : ℤ) (Q : SyntheticSpectrum) :
    BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
      BiHom (n - 1) (w + q) Q := by
  let e : BiHom (n - 1) (w + q) Q ≃
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
    simpa only [sub_add_cancel, add_neg_cancel_right] using
      ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
        (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
  exact e.symm


private abbrev biSuspensionHomEquiv := biSuspensionHomEquivRaw

private theorem bockstein_arrow_eq_biSuspensionIso_inv
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) :
    KIP126.Literature.bocksteinArrow background X q hq =
      ((background.quotients.tower (KIP126.Literature.nuZero background X)).triangle hq (Nat.lt_succ_self q)).delta ≫
        (biSuspensionIso (q : ℤ) (XModLambdaN (KIP126.Literature.nuZero background X) (q+1-q))).inv ≫
          eqToHom (congrArg (fun n => (SyntheticCategory.biShift (1,-(q:ℤ))).obj
            (XModLambdaN (KIP126.Literature.nuZero background X) n)) (show q+1-q=1 by omega)) := by
  have hcast {A A' B : SyntheticSpectrum} (h : A=A') (e : A ≅ B)
      (he : (A ≅ B) = (A' ≅ B)) :
      (he.mp e).inv = e.inv ≫ eqToHom h := by
    subst A'
    change e.inv = e.inv ≫ 𝟙 A
    exact (Category.comp_id _).symm
  simp only [KIP126.Literature.bocksteinArrow, biSuspensionIso]
  rw [hcast (congrArg (fun p : ℤ × ℤ => (SyntheticCategory.biShift p).obj
    (XModLambdaN (KIP126.Literature.nuZero background X) (q+1-q))) (by ext <;> simp))]
  simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Category.assoc, eqToHom_trans]


private theorem biSuspensionHomEquiv_eq_inverse_susp (n w q : ℤ) (Q : SyntheticSpectrum)
    (a : BiHom n w (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧)) :
    biSuspensionHomEquiv n w q Q a =
      (susp_invariance (n-1) (w+q) 1 (-q) Q).symm
        (homotopyRegrade (by omega) (by omega) (a ≫ (biSuspensionIso q Q).inv)) := by
  have hc (n' w' : ℤ) (hn : n' = n) (hw : w' = w)
      (e : BiHom (n-1) (w+q) Q ≃
        BiHom n' w' (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧))
      (he : (BiHom (n-1) (w+q) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧)) =
        (BiHom (n-1) (w+q) Q ≃
          BiHom n w (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧))) :
      (he.mp e).symm a = e.symm (homotopyRegrade hn.symm hw.symm a) := by
    subst n'
    subst w'
    rfl
  have regrade_comp {n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : SyntheticSpectrum}
      (a : BiHom n w A) (f : A ⟶ B) :
      homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
    subst n'
    subst w'
    rfl
  change biSuspensionHomEquivRaw n w q Q a = _
  unfold biSuspensionHomEquivRaw
  rw [hc (n-1+1) (w+q+-q) (by omega) (by omega)]
  rw [Equiv.symm_trans_apply, Iso.homCongr_symm, Iso.homCongr_apply]
  dsimp only [Iso.symm_hom, Iso.symm_inv, Iso.refl_hom]
  rw [Iso.refl_hom, Category.id_comp, regrade_comp]


private theorem firstLabel_bocksteinLabel_eq
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (KIP126.Literature.nuZero background X) q)) :
    KIP126.Literature.firstLabel background X (s+q+1) (t+q) (KIP126.Literature.bocksteinLabel background X q hq s t a) =
      homotopyRegrade (by omega) rfl
        ((susp_invariance (t-s-1) (t+q) 1 (-(q:ℤ)) _).symm
          (homotopyRegrade (by omega) (by omega) (a ≫ KIP126.Literature.bocksteinArrow background X q hq))) := by
  have regrade_cast {a b c d m n : ℤ} {Q : SyntheticSpectrum}
      (h1 : a=m) (h2 : b=n) (h3 : a=c) (h4 : b=d)
      (he : BiHom m n Q = BiHom c d Q) (x : BiHom a b Q) :
      he.mp (homotopyRegrade h1 h2 x) = homotopyRegrade h3 h4 x := by
    subst m; subst n; subst c; subst d
    rfl
  unfold KIP126.Literature.firstLabel KIP126.Literature.bocksteinLabel
  rw [LinearEquiv.symm_apply_apply]
  exact regrade_cast _ _ _ _ _ _


private theorem firstLabel_bocksteinLabel_eq_actual_delta
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (KIP126.Literature.nuZero background X) q)) :
    KIP126.Literature.firstLabel background X (s+q+1) (t+q) (KIP126.Literature.bocksteinLabel background X q hq s t a) =
      homotopyRegrade (by omega) rfl
        (biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN (KIP126.Literature.nuZero background X) (q+1-q))
          (a ≫ ((background.quotients.tower (KIP126.Literature.nuZero background X)).triangle hq (Nat.lt_succ_self q)).delta) ≫
          eqToHom (congrArg (fun n => XModLambdaN (KIP126.Literature.nuZero background X) n)
            (show q+1-q=1 by omega))) := by
  have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : SyntheticSpectrum}
      (a : BiHom n w A) (f : A ⟶ B) :
      homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
    subst n'; subst w'
    rfl
  have inverse_susp_cast {A B : SyntheticSpectrum} (h : A=B) (n w k l : ℤ)
      (b : BiHom (n+k) (w+l) ((SyntheticCategory.biShift (k,l)).obj A)) :
      (susp_invariance n w k l B).symm
        (b ≫ eqToHom (congrArg (SyntheticCategory.biShift (k,l)).obj h)) =
        (susp_invariance n w k l A).symm b ≫ eqToHom h := by
    subst B
    simp only [eqToHom_refl, Category.comp_id]
  rw [firstLabel_bocksteinLabel_eq, bockstein_arrow_eq_biSuspensionIso_inv,
    biSuspensionHomEquiv_eq_inverse_susp]
  repeat rw [regrade_comp]
  repeat rw [←Category.assoc]
  rw [inverse_susp_cast (congrArg (fun n => XModLambdaN (KIP126.Literature.nuZero background X) n)
    (show q+1-q=1 by omega))]
  rw [regrade_comp]

/-- The finite-quotient triangle's delta on the supplied lift, expressed
in bigraded first-quotient coordinates. -/
private def geometricBoundaryLabel (X : Spectrum) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q)) :
    BiHom ((t+q)-(s+q+1)) (t+q) (XModLambdaN (nuZeroSpectrum X) 1) :=
  homotopyRegrade (by omega) rfl
    (biSuspensionHomEquiv (t-s) t (q : ℤ)
      (XModLambdaN (nuZeroSpectrum X) (q+1-q))
      (a ≫ ((background.quotients.tower (nuZeroSpectrum X)).triangle hq
        (Nat.lt_succ_self q)).delta) ≫
      eqToHom (congrArg (fun n => XModLambdaN (nuZeroSpectrum X) n)
        (show q+1-q=1 by omega)))

/-- The delta coordinate formula identifies the geometric boundary
with the selected-object Bockstein label. -/
private theorem geometricBoundaryLabel_selected (X : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (nuZero background X) q)) :
    geometricBoundaryLabel (X.obj background.auxiliary) q hq s t a =
      firstLabel background X (s+q+1) (t+q) (bocksteinLabel background X q hq s t a) := by
  exact (firstLabel_bocksteinLabel_eq_actual_delta X q hq s t a).symm

/-- Geometric boundary formula for every spectrum, positive finite quotient
length, integer degree and lift. It identifies the E_(q+1) value of the lift's
restricted first-quotient label with its quotient-triangle boundary in the
fixed lambda-sequence coordinates. Earlier boundaries are included in the
page quotient. -/
private theorem lambda_geometric_boundary_input (X : Spectrum)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q)) :
    SyntheticHasDifferential (lambdaSS X) (q+1)
      (s,t,t-(0 : ℕ)) (s+q+1,t+q,(t+q)-q)
      ((baseInitialQuotientIso X s t 0).inv
        (a ≫ (background.quotients.tower (nuZeroSpectrum X)).rho 1 q hq))
      ((baseInitialQuotientIso X (s+q+1) (t+q) q).inv
        (geometricBoundaryLabel X q hq s t a)) := by
  sorry

end
end KIP126.Literature.Paper38BoundaryInput
end

@[expose] section
namespace KIP126.Literature.FiniteBoundaryComparison
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature.Paper38ComparisonInput
open KIP126.Literature.Paper38BoundaryInput
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

private theorem selected_classical_differential (X : AdamsObject (coefficients := background.coefficients))
    (s t : ℤ) (r k : ℕ) (hr : 2 ≤ r)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s+r,t+r-1)) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary)) r
      (s,t) (s+r,t+r-1) x y ↔
    SyntheticHasDifferential (lambdaSS (X.obj background.auxiliary)) r
      (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      ((baseInitialQuotientIso (X.obj background.auxiliary) s t k).inv
        (firstLabel background X s t x))
      ((baseInitialQuotientIso (X.obj background.auxiliary)
        (s+r) (t+r-1) (k+(r-1))).inv
          (firstLabel background X (s+r) (t+r-1) y)) := by
  have h := comparisonData.classical_differential (X.obj background.auxiliary) s t r k hr x y
  rw [comparisonData.classicalFirst_selected, comparisonData.classicalFirst_selected] at h
  exact h

private theorem selected_classical_finite_differential (X : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s+q+1,t+q)) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary)) (q+1)
      (s,t) (s+q+1,t+q) x y ↔
    SyntheticHasDifferential (lambdaSS (X.obj background.auxiliary)) (q+1)
      (s,t,t-0) (s+q+1,t+q,(t+q)-q)
      ((baseInitialQuotientIso (X.obj background.auxiliary) s t 0).inv
        (firstLabel background X s t x))
      ((baseInitialQuotientIso (X.obj background.auxiliary) (s+q+1) (t+q) q).inv
        (firstLabel background X (s+q+1) (t+q) y)) := by
  have h := selected_classical_differential X s t (q+1) 0 (by omega) x
  have hs : s + ((q+1 : ℕ) : ℤ) = s+q+1 := by omega
  have ht : t + ((q+1 : ℕ) : ℤ) - 1 = t+q := by omega
  have hk : (0 : ℕ)+(q+1-1) = q := by omega
  rw [hs, ht, hk] at h
  exact h y

private theorem bockstein_from_geometric_boundary
    (finite : FiniteLiftCriterion background) : BocksteinDifferential background := by
  intro X q hq s t x hx
  obtain ⟨a, ha⟩ := (finite X q hq s t x).mp hx
  refine ⟨a, ha, (selected_classical_finite_differential X q hq s t x
    (bocksteinLabel background X q hq s t a)).mpr ?_⟩
  have h := lambda_geometric_boundary_input (X.obj background.auxiliary) q hq s t a
  rw [ha, geometricBoundaryLabel_selected] at h
  exact h

end
end KIP126.Literature.FiniteBoundaryComparison
end
