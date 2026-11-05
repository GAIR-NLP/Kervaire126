module

import all KIP126.Literature.Standard.FiniteQuotientNoReturn

/-! Spherewise compatibility of finite-quotient and lambda-power
cofiber boundaries.
-/

@[expose] section
namespace KIP126.Literature.Standard.Internal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Kervaire.Route

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option Elab.async false

private theorem quotient_boundary_comparison
    (X : AdamsObject (coefficients := background.coefficients)) (i j : ℕ) (hi : 0 < i) (hij : i < j)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i)) :
    a ≫ ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).triangle
      hi hij).delta =
    a ≫ XModLambdaN.proj (background.nu.functor.obj (X.obj background.auxiliary)) i ≫
      (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -(i : ℤ))).map
          (XModLambdaN.incl (background.nu.functor.obj (X.obj background.auxiliary)) (j-i))) := by
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let T := (background.quotients.tower V).triangle hi hij
  obtain ⟨h, hh₁, hh₂⟩ := complete_distinguished_triangle_morphism
    (XModLambdaN.cofiberTriangle V i) (Triangle.mk T.lambdaMap T.rho T.delta)
    (XModLambdaN.cofiberTriangle_distinguished V i) T.distinguished
    ((SyntheticCategory.biShift (0, -(i : ℤ))).map (XModLambdaN.incl V (j-i)))
    (XModLambdaN.incl V j) T.lambda_quotient.symm
  change XModLambdaN.incl V i ≫ h = XModLambdaN.incl V j ≫ T.rho at hh₁
  rw [T.rho_quotient] at hh₁
  have hh : a ≫ h = a := by
    simpa only [Category.comp_id] using
      quotient_nu_maps_equal_on_spheres X X i hi h (𝟙 _) (by
        simpa only [Category.comp_id] using hh₁) m w a
  change XModLambdaN.proj V i ≫
    (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -(i : ℤ))).map (XModLambdaN.incl V (j-i))) =
    h ≫ T.delta at hh₂
  rw [hh₂, ← Category.assoc, hh]

private theorem quotient_nu_zero_endomorphism_on_spheres
    (X : AdamsObject (coefficients := background.coefficients)) (i : ℕ) (hi : 0 < i)
    (h : XModLambdaN (KIP126.Literature.nuZero background X) i ⟶
      XModLambdaN (KIP126.Literature.nuZero background X) i)
    (hh : XModLambdaN.incl _ i ≫ h = XModLambdaN.incl _ i)
    (m w : ℤ) (a : BiHom m w (XModLambdaN (KIP126.Literature.nuZero background X) i)) :
    a ≫ h = a := by
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let e : KIP126.Literature.nuZero background X ≅ V := SyntheticCategory.biShift_zero.app V
  let eQ := (background.quotients.functoriality.functor i).mapIso e
  have hinv : XModLambdaN.incl V i ≫ eQ.inv = e.inv ≫ XModLambdaN.incl _ i :=
    (XModLambdaN.incl_naturality e.inv i).symm
  have hhom : XModLambdaN.incl _ i ≫ eQ.hom = e.hom ≫ XModLambdaN.incl V i :=
    (XModLambdaN.incl_naturality e.hom i).symm
  have hg : XModLambdaN.incl V i ≫ (eQ.inv ≫ h ≫ eQ.hom) =
      XModLambdaN.incl V i ≫ 𝟙 _ := by
    rw [← Category.assoc, hinv]
    rw [Category.assoc, ← Category.assoc (XModLambdaN.incl _ i), hh, hhom]
    simp only [Iso.inv_hom_id_assoc, Category.comp_id]
  have hs := quotient_nu_maps_equal_on_spheres X X i hi
    (eQ.inv ≫ h ≫ eQ.hom) (𝟙 _) hg m w (a ≫ eQ.hom)
  apply (cancel_mono eQ.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using hs

/-- The canonical-boundary comparison on the zero-shift object used by
`firstLabel` and the BHS comparison. -/
private theorem quotient_nu_zero_boundary_comparison
    (X : AdamsObject (coefficients := background.coefficients)) (i j : ℕ) (hi : 0 < i) (hij : i < j)
    (m w : ℤ) (a : BiHom m w
      (XModLambdaN (KIP126.Literature.nuZero background X) i)) :
    a ≫ ((background.quotients.tower (KIP126.Literature.nuZero background X)).triangle hi hij).delta =
    a ≫ XModLambdaN.proj (KIP126.Literature.nuZero background X) i ≫
      (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -(i : ℤ))).map
          (XModLambdaN.incl (KIP126.Literature.nuZero background X) (j-i))) := by
  let V := KIP126.Literature.nuZero background X
  let T := (background.quotients.tower V).triangle hi hij
  obtain ⟨h, hh₁, hh₂⟩ := complete_distinguished_triangle_morphism
    (XModLambdaN.cofiberTriangle V i) (Triangle.mk T.lambdaMap T.rho T.delta)
    (XModLambdaN.cofiberTriangle_distinguished V i) T.distinguished
    ((SyntheticCategory.biShift (0, -(i : ℤ))).map (XModLambdaN.incl V (j-i)))
    (XModLambdaN.incl V j) T.lambda_quotient.symm
  change XModLambdaN.incl V i ≫ h = XModLambdaN.incl V j ≫ T.rho at hh₁
  rw [T.rho_quotient] at hh₁
  have hh := quotient_nu_zero_endomorphism_on_spheres X i hi h hh₁ m w a
  change XModLambdaN.proj V i ≫
    (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -(i : ℤ))).map (XModLambdaN.incl V (j-i))) =
    h ≫ T.delta at hh₂
  rw [hh₂, ← Category.assoc, hh]

/- Coordinate identities for the bigraded shifts. -/

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
  simp only [biSuspensionHomEquivRaw]
  rw [hc (n-1+1) (w+q+-q) (by omega) (by omega)]
  simp only [Equiv.symm_trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Category.id_comp, regrade_comp]


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
  simp only [KIP126.Literature.firstLabel, KIP126.Literature.bocksteinLabel, LinearEquiv.symm_apply_apply]
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
  simp only [regrade_comp, ←Category.assoc]
  rw [inverse_susp_cast (congrArg (fun n => XModLambdaN (KIP126.Literature.nuZero background X) n)
    (show q+1-q=1 by omega))]
  rw [regrade_comp]


private theorem biSuspensionIso_natural (i : ℤ) {A B : SyntheticSpectrum} (f : A ⟶ B) :
    (SyntheticCategory.biShift (1,-i)).map f ≫ (biSuspensionIso i B).hom =
      (biSuspensionIso i A).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
  let e : (SyntheticCategory.biShift ((0,-i)+(1,0)) : SyntheticSpectrum ⥤ SyntheticSpectrum) ≅
      SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor SyntheticSpectrum (1:ℤ) :=
    (SyntheticCategory.biShift_comp (0,-i) (1,0)).symm ≪≫
      Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-i)) (SyntheticCategory.biShift_compat 1)
  have cast_natural (p p' : ℤ×ℤ) (hp : p=p')
      (E : (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum) ≅
        SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor SyntheticSpectrum (1:ℤ))
      (hA : ((SyntheticCategory.biShift p).obj A ≅
        (shiftFunctor SyntheticSpectrum (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)) =
        ((SyntheticCategory.biShift p').obj A ≅
        (shiftFunctor SyntheticSpectrum (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)))
      (hB : ((SyntheticCategory.biShift p).obj B ≅
        (shiftFunctor SyntheticSpectrum (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B)) =
        ((SyntheticCategory.biShift p').obj B ≅
        (shiftFunctor SyntheticSpectrum (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B))) :
      (SyntheticCategory.biShift p').map f ≫ (cast hB (E.app B)).hom =
        (cast hA (E.app A)).hom ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
    subst p'
    exact E.hom.naturality f
  unfold biSuspensionIso
  exact cast_natural ((0,-i)+(1,0)) (1,-i) (by ext <;> simp) e _ _


private theorem biSuspensionHomEquiv_natural (n w q : ℤ) {A B : SyntheticSpectrum} (f : A ⟶ B)
    (a : BiHom n w (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧)) :
    biSuspensionHomEquiv n w q B
        (a ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((SyntheticCategory.biShift (0,-q)).map f)) =
      biSuspensionHomEquiv n w q A a ≫ f := by
  have susp_nat (n w k l : ℤ) (b : BiHom n w A) :
      susp_invariance n w k l A b ≫ (SyntheticCategory.biShift (k,l)).map f =
        susp_invariance n w k l B (b ≫ f) := by
    change ((SyntheticCategory.biShift_comp (n,w) (k,l)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (k,l)).map b ≫ 𝟙 _) ≫ _ =
      _ ≫ (SyntheticCategory.biShift (k,l)).map (b ≫ f) ≫ 𝟙 _
    simp only [Functor.map_comp, Category.comp_id, Category.assoc, Iso.app_inv]
  have inv_susp_nat (n w k l : ℤ)
      (b : BiHom (n+k) (w+l) ((SyntheticCategory.biShift (k,l)).obj A)) :
      (susp_invariance n w k l B).symm (b ≫ (SyntheticCategory.biShift (k,l)).map f) =
        (susp_invariance n w k l A).symm b ≫ f := by
    apply (susp_invariance n w k l B).injective
    rw [Equiv.apply_symm_apply, ←susp_nat, Equiv.apply_symm_apply]
  have hi : (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((SyntheticCategory.biShift (0,-q)).map f) ≫
      (biSuspensionIso q B).inv =
      (biSuspensionIso q A).inv ≫ (SyntheticCategory.biShift (1,-q)).map f := by
    apply (cancel_mono (biSuspensionIso q B).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [biSuspensionIso_natural]
    simp only [Iso.inv_hom_id_assoc]
  have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : SyntheticSpectrum}
      (a : BiHom n w A) (f : A ⟶ B) :
      homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
    subst n'; subst w'
    rfl
  rw [biSuspensionHomEquiv_eq_inverse_susp, biSuspensionHomEquiv_eq_inverse_susp]
  simp only [Category.assoc]
  rw [hi, ←Category.assoc, regrade_comp, inv_susp_nat]
/-- The actual finite Bockstein boundary is the first-quotient image of
an actual class of the same zero-shifted synthetic analogue. -/
private theorem boundary_label_factors_through_nu
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (KIP126.Literature.nuZero background X) q)) :
    ∃ b : BiHom ((t+q)-(s+q+1)) (t+q) (KIP126.Literature.nuZero background X),
      KIP126.Literature.firstLabel background X (s+q+1) (t+q)
        (KIP126.Literature.bocksteinLabel background X q hq s t a) =
      b ≫ XModLambdaN.incl _ 1 := by
  refine ⟨homotopyRegrade (by omega) rfl
    (biSuspensionHomEquiv (t-s) t (q:ℤ) (KIP126.Literature.nuZero background X)
      (a ≫ XModLambdaN.proj _ q)), ?_⟩
  rw [firstLabel_bocksteinLabel_eq_actual_delta,
    quotient_nu_zero_boundary_comparison, ← Category.assoc a,
    biSuspensionHomEquiv_natural]
  have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : SyntheticSpectrum}
      (a : BiHom n w A) (f : A ⟶ B) :
      homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
    subst n'; subst w'
    rfl
  have incl_cast (V : SyntheticSpectrum) (n n' : ℕ) (h : n=n') :
      XModLambdaN.incl V n ≫ eqToHom (congrArg (fun k => XModLambdaN V k) h) =
        XModLambdaN.incl V n' := by
    subst n'
    simp only [eqToHom_refl, Category.comp_id]
  simp only [regrade_comp, Category.assoc]
  rw [incl_cast _ _ _ (by omega)]

/-- A boundary target has a single nu class supplying compatible
lifts through every positive finite quotient. -/
private theorem boundary_label_lifts_to_all_finite_quotients
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (KIP126.Literature.nuZero background X) q))
    (n : ℕ) (hn : 0 < n) :
    ∃ b : BiHom ((t+q)-(s+q+1)) (t+q)
      (XModLambdaN (KIP126.Literature.nuZero background X) n),
      b ≫ (background.quotients.tower (KIP126.Literature.nuZero background X)).rho 1 n hn =
        KIP126.Literature.firstLabel background X (s+q+1) (t+q)
          (KIP126.Literature.bocksteinLabel background X q hq s t a) := by
  obtain ⟨b,hb⟩ := boundary_label_factors_through_nu X q hq s t a
  refine ⟨b ≫ XModLambdaN.incl _ n, ?_⟩
  rw [Category.assoc, FiniteLambdaQuotientTower.rho_quotient]
  exact hb.symm

end
end KIP126.Literature.Standard.Internal
