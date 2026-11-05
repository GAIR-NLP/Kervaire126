module
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.GeneralizedMahowald.Signs
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn

/-! May correction for a nu-source that is a bigraded sphere.
Every quotient extension and both corrections are maps in the selected model. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem shifted_nu_to_shifted_finite_no_return (X Y : AdamsObject (coefficients := background.coefficients))
    (r : ℕ) (hr : 0<r) (δ ε : ℤ×ℤ)
    (hgap : (r:ℤ)≤δ.1-δ.2-(ε.1-ε.2)) (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary))))
    (z : (SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      (SyntheticCategory.biShift ε).obj
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) r)) : c≫z=0 := by
  let A : SyntheticObject (coefficients := background.coefficients) := .shift δ (.nu X)
  let B : SyntheticObject (coefficients := background.coefficients) := .shift ε (.quotient r (.nu Y))
  let L : ℤ := w-m+δ.1-δ.2
  have hzA (k : ℤ) (hk : k<L) :
      IsZero (((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData (k,m+k,w)).eInfty) := by
    have hz := nu_infinity_zero_above X k (m-δ.1+k) (w-δ.2)
      (by dsimp [L] at hk; omega)
    let e := towerInfinityIso (background.convergence (.nu X)) (background.convergence A)
      ((essShift δ).filtered (.nu X) (m-δ.1,w-δ.2)) k
    have he := hz.of_iso e.symm
    simpa only [e,A,Prod.fst_add,Prod.snd_add,sub_add_cancel] using he
  have hc0 := filtration_at_zero background.syntheticTower _ m w c
  have hcL : FiltrationAtLeast background.syntheticTower L c := by
    by_cases hL : L≤0
    · exact background.syntheticTower.filtrationSubmodule_antitone _ (m,w) hL hc0
    · exact (filtration_iff_of_infinity_zero (background.convergence A) 0 L m w
        (by omega) (fun k _ hk => hzA k hk) c).mp hc0
  have hcz := map_preserves_filtration (background.convergentMap A B z) (m,w) L c hcL
  have hzB (k : ℤ) (hk : L≤k) :
      IsZero (((background.family.obj (B.obj background.nu background.auxiliary)).sequence.ssData (k,m+k,w)).eInfty) := by
    have hz := finite_infinity_zero_outside Y r hr k (m-ε.1+k) (w-ε.2)
      (by dsimp [L] at hk; omega)
    let e := towerInfinityIso (background.convergence (.quotient r (.nu Y))) (background.convergence B)
      ((essShift ε).filtered (.quotient r (.nu Y)) (m-ε.1,w-ε.2)) k
    have he := hz.of_iso e.symm
    simpa only [e,B,Prod.fst_add,Prod.snd_add,sub_add_cancel] using he
  apply shifted_quotient_homotopy_separated (.nu Y) r ε m w (c≫z)
  intro k
  by_cases hk : L≤(k:ℤ)
  · exact (filtration_iff_of_infinity_zero (background.convergence B) L k m w hk
      (fun j hj _ => hzB j hj) (c≫z)).mp hcz
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hcz

/- Into the high shifted final quotient, any two actual finite-source
extensions agreeing before quotienting have identical action on all spheres. -/
private theorem finite_source_high_target_extensions_equal
    (X Y : AdamsObject (coefficients := background.coefficients)) (q r : ℕ) (hr : 0<r) (a b : ℤ)
    (hgap : (r:ℤ)≤q+b-a+1)
    (u v : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) r))
    (hincl : XModLambdaN.incl _ q≫u=XModLambdaN.incl _ q≫v)
    (m w : ℤ)
    (c : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q)) : c≫u=c≫v := by
  apply quotient_maps_equal_on_spheres_of_no_return q u v hincl
  intro m' w' d z
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let ε : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj
      ((SyntheticCategory.biShift (0,a)).obj V)))⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (1,a-q)).obj V :=
    (biSuspensionIso (q:ℤ) ((SyntheticCategory.biShift (0,a)).obj V)).symm ≪≫
      (SyntheticCategory.biShift_comp (0,a) (1,-(q:ℤ))).app V ≪≫
      eqToIso (by simp [sub_eq_add_neg])
  have hz := shifted_nu_to_shifted_finite_no_return X Y r hr (1,a-q) (0,b)
    (by dsimp; omega) m' w' (d≫ε.hom) (ε.inv≫z)
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hz


private theorem sphere_nu_high_target_map_zero
    (Y X : AdamsObject (coefficients := background.coefficients)) (n w₀ a b : ℤ) (r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤b-a)
    (eY : background.nu.functor.obj (Y.obj background.auxiliary) ≅ Smn n w₀)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) r)) : d=0 := by
  let e : (SyntheticCategory.biShift (0,a)).obj
      (background.nu.functor.obj (Y.obj background.auxiliary)) ≅ Smn n (w₀+a) :=
    (SyntheticCategory.biShift (0,a)).mapIso eY ≪≫
      (SyntheticCategory.biShift_comp (n,w₀) (0,a)).app S_0_0 ≪≫
      eqToIso (by simp [Smn])
  apply (cancel_epi e.inv).mp
  simpa only [comp_zero] using
    shifted_nu_to_shifted_finite_no_return Y X r hr (0,a) (0,b)
      (by dsimp; omega) n (w₀+a) e.inv d

private theorem sphere_nu_high_target_extension
    (Y X : AdamsObject (coefficients := background.coefficients)) (n w₀ a b : ℤ) (q r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤q+b-a)
    (eY : background.nu.functor.obj (Y.obj background.auxiliary) ≅ Smn n w₀)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) r)) :
    ∃ dQ : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (background.nu.functor.obj (Y.obj background.auxiliary))) q ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) r),
      XModLambdaN.incl _ q≫dQ=d := by
  let V := background.nu.functor.obj (Y.obj background.auxiliary)
  let A := (SyntheticCategory.biShift (0,a)).obj V
  let ε : (SyntheticCategory.biShift (0,-(q:ℤ))).obj A ≅
      (SyntheticCategory.biShift (0,a-q)).obj V :=
    (SyntheticCategory.biShift_comp (0,a) (0,-(q:ℤ))).app V ≪≫
      eqToIso (by simp [sub_eq_add_neg])
  have hz := sphere_nu_high_target_map_zero Y X n w₀ (a-q) b r hr
    (by omega) eY (ε.inv≫lambdaPow q A≫d)
  have hzero : lambdaPow q A≫d=0 := by
    apply (cancel_epi ε.inv).mp
    simpa only [comp_zero] using hz
  obtain ⟨dQ,hdQ⟩ := (XModLambdaN.cofiberTriangle A q).yoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished A q) d hzero
  exact ⟨dQ,hdQ.symm⟩

private theorem detects_zero_of_detects_same_label_zero
    (D : SyntheticObject (coefficients := background.coefficients)) (p : Tridegree)
    (x : (background.family.obj (D.obj background.nu background.auxiliary)).E₂ p)
    (a : BiHom (p.2.1-p.1) p.2.2 (D.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence D) p x a)
    (hzero : Detects (background.convergence D) p x 0) :
    Detects (background.convergence D) p 0 a := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨e0,he0,b,hb,hgb⟩ := hzero
  have hb0 : b=0 := (ModuleCat.mono_iff_injective
    ((background.syntheticTower.filtration (D.obj background.nu background.auxiliary)).F p.1
      (p.2.1-p.1,p.2.2)).arrow).mp inferInstance (hb.trans (map_zero _).symm)
  have he00 : e0=0 := ((background.convergence D).identification p).toLinearEquiv.injective (by
    change ((background.convergence D).identification p).hom e0 =
      ((background.convergence D).identification p).hom 0
    rw [hgb,hb0,map_zero,map_zero])
  have hee : e=0 := (he.unique he0).trans he00
  refine ⟨0,HasInfinityRepresentative.zero _ 2 (by omega) p,a',ha',?_⟩
  simpa only [hee] using hga


/- Elementwise May correction for a sphere source. Triangle exactness
extends both defects through Qq, giving correction alpha dQ
for the specified alpha. -/
private theorem sphere_source_actual_edge_correction
    (Y X Z : AdamsObject (coefficients := background.coefficients)) (n w₀ a b cWeight : ℤ)
    (q r i : ℕ) (hr : 0 < r) (hi : 0 < i)
    (hgapC : (r:ℤ)≤q+b-a) (hgapD : (r:ℤ)≤q+cWeight-a)
    (hkill : (i:ℤ)≤b-a)
    (eY : background.nu.functor.obj (Y.obj background.auxiliary) ≅ Smn n w₀)
    (A C D : SyntheticObject (coefficients := background.coefficients))
    (hA : A=.shift (0,a) (.nu Y))
    (hC : C=.shift (0,b) (.quotient r (.nu X)))
    (hD : D=.shift (0,cWeight) (.quotient r (.nu Z)))
    (d : A.obj background.nu background.auxiliary ⟶ C.obj background.nu background.auxiliary)
    (h : C.obj background.nu background.auxiliary ⟶ D.obj background.nu background.auxiliary)
    (R : A.obj background.nu background.auxiliary ⟶ D.obj background.nu background.auxiliary)
    (K J : (SyntheticObject.quotient q A).obj background.nu background.auxiliary ⟶ D.obj background.nu background.auxiliary)
    (rho : C.obj background.nu background.auxiliary ⟶ (SyntheticCategory.biShift (0,b)).obj
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i))
    (hedge : XModLambdaN.incl (A.obj background.nu background.auxiliary) q≫K-
      XModLambdaN.incl (A.obj background.nu background.auxiliary) q≫J=d≫h-R)
    (p : Tridegree) (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ p)
    (alpha : BiHom (p.2.1-p.1) p.2.2 ((SyntheticObject.quotient q A).obj background.nu background.auxiliary))
    (v : BiHom (p.2.1-p.1) p.2.2 (C.obj background.nu background.auxiliary))
    (halpha : Detects (background.convergence (SyntheticObject.quotient q A)) p
      (familyPageMap background.family (XModLambdaN.incl (A.obj background.nu background.auxiliary) q) 2 p x) alpha)
    (hv : v≫h=alpha≫K)
    (hRzero : Detects (background.convergence D) p (familyPageMap background.family R 2 p x) 0) :
    ∃ (dQ : (SyntheticObject.quotient q A).obj background.nu background.auxiliary ⟶ C.obj background.nu background.auxiliary)
      (v' : BiHom (p.2.1-p.1) p.2.2 (C.obj background.nu background.auxiliary)),
      XModLambdaN.incl (A.obj background.nu background.auxiliary) q≫dQ=d ∧ v'=v-alpha≫dQ ∧
      Detects (background.convergence C) p (familyPageMap background.family d 2 p x) (alpha≫dQ) ∧
      v'≫rho=v≫rho ∧
      Detects (background.convergence D) p
        (familyPageMap background.family J 2 p
          (familyPageMap background.family (XModLambdaN.incl (A.obj background.nu background.auxiliary) q) 2 p x)) (v'≫h) := by
  subst A
  subst C
  subst D
  dsimp only [SyntheticObject.obj] at d h R K J rho x alpha v halpha hv hedge hRzero ⊢
  obtain ⟨dQ,hdQ⟩ := sphere_nu_high_target_extension Y X n w₀ a b q r hr hgapC eY d
  obtain ⟨RQ,hRQ⟩ := sphere_nu_high_target_extension Y Z n w₀ a cWeight q r hr hgapD eY R
  have hdRho : d≫rho=0 := sphere_nu_high_target_map_zero Y X n w₀ a b i hi hkill eY (d≫rho)
  have hincRho : XModLambdaN.incl _ q≫(dQ≫rho)=XModLambdaN.incl _ q≫0 := by
    rw [←Category.assoc,hdQ,hdRho,comp_zero]
  have hcdRho : (alpha≫dQ)≫rho=0 := by
    have heq := finite_source_high_target_extensions_equal Y X q i hi a b
      (by omega) (dQ≫rho) 0 hincRho (p.2.1-p.1) p.2.2 alpha
    simpa only [Category.assoc,comp_zero] using heq
  have hinc : XModLambdaN.incl _ q≫(K-J) = XModLambdaN.incl _ q≫(dQ≫h-RQ) := by
    simp only [Preadditive.comp_sub,←Category.assoc,hdQ,hRQ]
    exact hedge
  have heq := finite_source_high_target_extensions_equal Y Z q r hr a cWeight
    (by omega) (K-J) (dQ≫h-RQ) hinc (p.2.1-p.1) p.2.2 alpha
  have heq' : alpha≫K-alpha≫J=(alpha≫dQ)≫h-alpha≫RQ := by
    simpa only [Preadditive.comp_sub,Category.assoc] using heq
  have hmath : (v-alpha≫dQ)≫h=alpha≫J-alpha≫RQ := by
    rw [Preadditive.sub_comp,hv]
    calc
      alpha≫K-(alpha≫dQ)≫h = (alpha≫K-alpha≫J)+alpha≫J-(alpha≫dQ)≫h := by abel
      _ = ((alpha≫dQ)≫h-alpha≫RQ)+alpha≫J-(alpha≫dQ)≫h := by rw [heq']
      _ = alpha≫J-alpha≫RQ := by abel
  have hdLabel : familyPageMap background.family dQ 2 p
      (familyPageMap background.family (XModLambdaN.incl _ q) 2 p x) =
      familyPageMap background.family d 2 p x := by
    rw [←ModuleCat.comp_apply,family_page_comp,hdQ]
  have hRLabel : familyPageMap background.family RQ 2 p
      (familyPageMap background.family (XModLambdaN.incl _ q) 2 p x) =
      familyPageMap background.family R 2 p x := by
    rw [←ModuleCat.comp_apply,family_page_comp,hRQ]
  have hcd := detects_map (.quotient q (.shift (0,a) (.nu Y)))
    (.shift (0,b) (.quotient r (.nu X))) dQ p _ alpha halpha
  have hcd := (congrArg (fun z => Detects
    (background.convergence (.shift (0,b) (.quotient r (.nu X)))) p z (alpha≫dQ)) hdLabel).mp hcd
  have hres := detects_map (.quotient q (.shift (0,a) (.nu Y)))
    (.shift (0,cWeight) (.quotient r (.nu Z))) RQ p _ alpha halpha
  have hres := (congrArg (fun z => Detects
    (background.convergence (.shift (0,cWeight) (.quotient r (.nu Z)))) p z (alpha≫RQ)) hRLabel).mp hres
  have hres0 := detects_zero_of_detects_same_label_zero
    (.shift (0,cWeight) (.quotient r (.nu Z))) p _ _ hres hRzero
  have hJ := detects_map (.quotient q (.shift (0,a) (.nu Y)))
    (.shift (0,cWeight) (.quotient r (.nu Z))) J p _ alpha halpha
  have htarget := detects_add (background.convergence (.shift (0,cWeight) (.quotient r (.nu Z))))
    p hJ (detects_neg hres0)
  refine ⟨dQ,v-alpha≫dQ,hdQ,rfl,hcd,?_,?_⟩
  · rw [Preadditive.sub_comp,hcdRho,sub_zero]
  · rw [hmath]
    simpa only [SyntheticObject.obj,neg_zero,add_zero,sub_eq_add_neg] using htarget

end
end KIP126.ProofTools.Internal.Mahowald
