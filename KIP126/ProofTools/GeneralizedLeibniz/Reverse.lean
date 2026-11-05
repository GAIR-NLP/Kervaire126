module
import all KIP126.ProofTools.GeneralizedLeibniz.Survival
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels

/-! The reverse absolute-boundary comparison used in AimPaper
Proposition `prop:6de7d130` and Theorem 6.1. Equal first restrictions force
the difference of adjacent absolute boundaries to be λ torsion of the exact
order giving the classical boundary indeterminacy. The higher-quotient lift
then identifies the differential target of any specified representative. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem first_label_lift_permanent (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (y : Ambient background X (s,t))
    (α : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = firstLabel background X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    y ∈ permanentCycles background X (s,t) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let inv : A ⟶ nuZero background X := SyntheticCategory.biShift_zero.inv.app A
  have hfirst : quotientClass 1 (α ≫ inv) = firstLabel background X s t y := by
    dsimp only [quotientClass]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hα,
      Category.assoc,←background.quotients.functoriality.map_comp]
    simp only [inv,A,Iso.hom_inv_id_app,background.quotients.functoriality.map_id,Category.comp_id]
  obtain ⟨z,hz⟩ := (KIP126.Literature.Standard.permanent_lift X s t y).mpr
    ⟨α ≫ inv,hfirst⟩
  refine ⟨z,?_⟩
  have h := normalizeInitialProjection ((background.classical.obj (X.obj background.auxiliary)).ssData (s,t))
    (↑(2-(background.classical.obj (X.obj background.auxiliary)).r₀).toNat)
    ⊤ (by rw [background.classical.firstPage]; rfl) le_top
  exact (congrArg (fun f => f z) h).symm.trans hz

private theorem detected_zero_infinity (A : SyntheticObject (coefficients := background.coefficients)) (p : Tridegree)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ p)
    (h : Detects (background.convergence A) p x 0) :
    HasInfinityRepresentative _ 2 p x 0 := by
  obtain ⟨e,he,a,ha,hga⟩ := h
  have haz : a = 0 := (ModuleCat.mono_iff_injective
    ((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F p.1 (p.2.1-p.1,p.2.2)).arrow).mp
      inferInstance (ha.trans (map_zero _).symm)
  have hez : e = 0 := ((background.convergence A).identification p).toLinearEquiv.injective (by
    change ((background.convergence A).identification p).hom e =
      ((background.convergence A).identification p).hom 0
    rw [hga,haz,map_zero,map_zero])
  rwa [hez] at he

private theorem first_label_lambda_zero_boundary (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (k : ℕ) (hk : 0 < k) (y : Ambient background X (s,t))
    (α : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = firstLabel background X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hz : lambdaMultiply k α = 0) :
    y ∈ boundaries background X (k+1) (s,t) := by
  have hy := first_label_lift_permanent X s t y α hα
  have hd := nu_lambda_detects X k hk s t y hy α hα
  rw [hz] at hd
  have he := detected_zero_infinity (.nu X) (s,t,t-k) _ hd
  have hclass := (KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-k) (by omega) y 0).mp he
  have hb := (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hclass.1⟩).mp (by
    rw [←hclass.2,map_zero])
  convert hb using 1
  congr 1
  omega

private theorem firstLabel_sub (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x y : Ambient background X (s,t)) :
    firstLabel background X s t (x-y) = firstLabel background X s t x - firstLabel background X s t y := by
  have cast_sub (m w w' : ℤ) (A : SyntheticSpectrum) (hw : w = w')
      (he : BiHom m w A = BiHom m w' A) (a b : BiHom m w A) :
      he.mp (a-b) = he.mp a - he.mp b := by
    subst w'; rfl
  simp only [firstLabel,map_sub]
  exact cast_sub _ _ _ _ (Int.add_zero t) _ _ _

private theorem first_label_zero (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (y : Ambient background X (s,t))
    (hy : firstLabel background X s t y ≫ XModLambdaN.map
      (SyntheticCategory.biShift_zero.hom.app _) 1 = 0) : y = 0 := by
  have hfirst : (0 : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary))) ≫
      XModLambdaN.incl _ 1 = firstLabel background X s t y ≫ XModLambdaN.map
      (SyntheticCategory.biShift_zero.hom.app _) 1 := by rw [zero_comp,hy]
  have hp := first_label_lift_permanent X s t y 0 hfirst
  have hd := nu_first_label_detects X s t y hp 0 hfirst
  have he := detected_zero_infinity (.nu X) (s,t,t) _ hd
  have hc := (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) y 0).mp he
  have hb := (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hc.1⟩).mp (by rw [←hc.2,map_zero])
  simpa only [add_sub_cancel_right,boundaries_one,Submodule.mem_bot] using hb

private def boundaryRepresentative (X : AdamsObject (coefficients := background.coefficients)) (k : ℕ) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) k)) :
    BiHom ((t+k)-(s+k+1)) (t+k) (background.nu.functor.obj (X.obj background.auxiliary)) :=
  homotopyRegrade (by omega) rfl
    (biSuspensionHomEquiv (t-s) t k (background.nu.functor.obj (X.obj background.auxiliary))
      (a ≫ XModLambdaN.proj _ k))

private theorem boundaryRepresentative_sub (X : AdamsObject (coefficients := background.coefficients)) (k : ℕ) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) k)) :
    boundaryRepresentative X k s t (a-b) =
      boundaryRepresentative X k s t a - boundaryRepresentative X k s t b := by
  simp only [boundaryRepresentative,Preadditive.sub_comp,map_sub,regrade_precomp,Preadditive.comp_sub]

private theorem first_restriction_kernel_boundary_lambda_zero (X : AdamsObject (coefficients := background.coefficients))
    (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) k))
    (ha : a ≫ (background.quotients.tower _).rho 1 k hk = 0) :
    lambdaMultiply (k-1) (boundaryRepresentative X k s t a) = 0 := by
  have hres := absolute_boundary_restriction X 1 k hk (t-s) t a
  rw [ha,zero_comp,map_zero] at hres
  have hzero : lambdaMultiply (k-1)
      (biSuspensionHomEquiv (t-s) t k (background.nu.functor.obj (X.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ k)) = 0 := by
    simpa only [regrade_precomp,comp_eq_zero_iff_of_epi] using hres.symm
  dsimp only [boundaryRepresentative]
  rw [lambda_regrade,hzero]
  simp only [regrade_precomp,comp_zero]

private theorem adjacent_boundary_labels_congruent (X : AdamsObject (coefficients := background.coefficients))
    (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) k))
    (hab : a ≫ (background.quotients.tower _).rho 1 k hk =
      b ≫ (background.quotients.tower _).rho 1 k hk)
    (y z : Ambient background X (s+k+1,t+k))
    (hy : boundaryRepresentative X k s t a ≫ XModLambdaN.incl _ 1 =
      firstLabel background X (s+k+1) (t+k) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hz : boundaryRepresentative X k s t b ≫ XModLambdaN.incl _ 1 =
      firstLabel background X (s+k+1) (t+k) z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    y-z ∈ boundaries background X k (s+k+1,t+k) := by
  have hfirst : boundaryRepresentative X k s t (a-b) ≫ XModLambdaN.incl _ 1 =
      firstLabel background X (s+k+1) (t+k) (y-z) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [boundaryRepresentative_sub,Preadditive.sub_comp,hy,hz,firstLabel_sub,Preadditive.sub_comp]
  by_cases hk1 : k=1
  · subst k
    have hab' : a=b := by simpa only [(background.quotients.tower _).rho_id,Category.comp_id] using hab
    have hzero : y-z=0 := first_label_zero X (s+(1:ℕ)+1) (t+(1:ℕ)) (y-z) (by
      rw [←hfirst,hab',sub_self]
      simp only [boundaryRepresentative,zero_comp,map_zero,regrade_precomp,comp_zero])
    rw [hzero]
    exact Submodule.zero_mem _
  have hmul := first_restriction_kernel_boundary_lambda_zero X k hk s t (a-b) (by
    rw [Preadditive.sub_comp,hab,sub_self])
  have hb := first_label_lambda_zero_boundary X (s+k+1) (t+k) (k-1) (by omega) (y-z)
    (boundaryRepresentative X k s t (a-b)) hfirst hmul
  simpa only [Nat.cast_sub hk,Nat.cast_one,sub_add_cancel] using hb

private theorem adjacent_boundary_differential (X : AdamsObject (coefficients := background.coefficients))
    (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+k+1,t+k))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) k))
    (ha : a ≫ (background.quotients.tower _).rho 1 k hk =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hy : boundaryRepresentative X k s t a ≫ XModLambdaN.incl _ 1 =
      firstLabel background X (s+k+1) (t+k) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  have hx := first_label_lift_cycles X k hk s t x a ha
  have hreach := (isCycle_iff_reaches background X (k+1) (by omega) (s,t) x).mp
    ⟨by omega,by simpa only [add_sub_cancel_right] using hx⟩
  obtain ⟨b,hb,hdb⟩ := KIP126.Literature.Standard.bockstein_differential X k hk s t x hreach
  let z := bocksteinLabel background X k hk s t b
  obtain ⟨a0,ha0,hz⟩ := adjacent_absolute_boundary X k hk s t x z hdb
  have hcong := adjacent_boundary_labels_congruent X k hk s t a a0 (ha.trans ha0.symm) y z hy hz
  exact (differentialAt_of_congruent background X
    (⟨by omega,hdb⟩ : DifferentialAt background X (k+1) (s,t) (s+k+1,t+k) x z)
    ⟨by omega,by simpa only [add_sub_cancel_right] using hcong⟩).2

private theorem firstLabel_surjective (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) :
    Function.Surjective (firstLabel background X s t) := by
  have cast_surjective (m w w' : ℤ) (A : SyntheticSpectrum) (hw : w = w')
      (he : BiHom m w A = BiHom m w' A) : Function.Surjective he.mp := by
    subst w'; exact Function.surjective_id
  have hs := (cast_surjective (t-s) (t+0) t (XModLambdaN (nuZero background X) 1)
    (Int.add_zero t) (by simp)).comp (background.firstQuotient X 0 s t).symm.surjective
  exact hs

private theorem nu_first_label_exists (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (α : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary))) :
    ∃ y : Ambient background X (s,t),
      α ≫ XModLambdaN.incl _ 1 = firstLabel background X s t y ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  obtain ⟨y,hy⟩ := firstLabel_surjective X s t
    (α ≫ XModLambdaN.incl A 1 ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) 1)
  refine ⟨y,?_⟩
  rw [hy,Category.assoc,Category.assoc,←background.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app,background.quotients.functoriality.map_id]
  simp only [Functor.id_obj,Category.comp_id]
  rfl

private theorem nu_detected_labels_congruent (X : AdamsObject (coefficients := background.coefficients)) (s t w : ℤ)
    (hw : w ≤ t) (y z : Ambient background X (s,t))
    (α : BiHom (t-s) w (background.nu.functor.obj (X.obj background.auxiliary)))
    (hy : Detects (background.convergence (.nu X)) (s,t,w) (nuWeightLabel background X s t w hw y) α)
    (hz : Detects (background.convergence (.nu X)) (s,t,w) (nuWeightLabel background X s t w hw z) α) :
    y-z ∈ boundaries background X (1+t-w) (s,t) := by
  obtain ⟨ey,hey,a,ha,hga⟩ := hy
  obtain ⟨ez,hez,b,hb,hgb⟩ := hz
  have hab : a = b := (ModuleCat.mono_iff_injective
    ((background.syntheticTower.filtration (background.nu.functor.obj (X.obj background.auxiliary))).F s (t-s,w)).arrow).mp
      inferInstance (ha.trans hb.symm)
  have heq : ey = ez := ((background.convergence (.nu X)).identification (s,t,w)).toLinearEquiv.injective (by
    change ((background.convergence (.nu X)).identification (s,t,w)).hom ey =
      ((background.convergence (.nu X)).identification (s,t,w)).hom ez
    rw [hga,hgb,hab])
  obtain ⟨hyp,hycl⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw y ey).mp hey
  obtain ⟨hzp,hzcl⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw z ez).mp hez
  have hequal : subquotientClass (permanentCycles background X (s,t)) (boundaries background X (1+t-w) (s,t)) ⟨y,hyp⟩ =
      subquotientClass (permanentCycles background X (s,t)) (boundaries background X (1+t-w) (s,t)) ⟨z,hzp⟩ := by
    rw [←hycl,←hzcl,heq]
  have hzero : subquotientClass (permanentCycles background X (s,t)) (boundaries background X (1+t-w) (s,t))
      (⟨y,hyp⟩ - ⟨z,hzp⟩) = 0 := by rw [map_sub,hequal,sub_self]
  exact (CrossingLabels.subquotient_zero_iff _ _ _).mp hzero

private theorem detects_filtration (A : SyntheticObject (coefficients := background.coefficients)) (p : Tridegree)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ p)
    (a : BiHom (p.2.1-p.1) p.2.2 (A.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence A) p x a) : FiltrationAtLeast background.syntheticTower p.1 a := by
  obtain ⟨e,he,b,hb,hgb⟩ := ha
  have hm : a ∈ ModuleCat.subobjectModule _ ((background.syntheticTower.filtration
      (A.obj background.nu background.auxiliary)).F p.1 (p.2.1-p.1,p.2.2)) := ⟨b,hb⟩
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm

private theorem boundary_detects_differential (X : AdamsObject (coefficients := background.coefficients))
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+k+1,t+k))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i))
    (ha : a ≫ (background.quotients.tower _).rho 1 i hi =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hy : Detects (background.convergence (.nu X)) (s+k+1,t+k,t+i)
      (nuWeightLabel background X (s+k+1) (t+k) (t+i) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ i)))) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have hfil : FiltrationAtLeast background.syntheticTower (s+k+1)
      (biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i)) := by
    have hf := detects_filtration (.nu X) (s+k+1,t+k,t+i) _ _ hy
    have transport (m m' w s : ℤ) (hm : m=m') (a : BiHom m w A) :
        FiltrationAtLeast background.syntheticTower s (homotopyRegrade hm rfl a) ↔
          FiltrationAtLeast background.syntheticTower s a := by subst m'; rfl
    exact (transport _ _ _ _ _ _).mp hf
  obtain ⟨b,hb⟩ : ∃ b : BiHom (t-s) t (XModLambdaN A k),
      b ≫ (background.quotients.tower A).rho i k hik = a := by
    rcases hik.eq_or_lt with rfl | hlt
    · exact ⟨a,by rw [(background.quotients.tower A).rho_id,Category.comp_id]⟩
    · exact absolute_boundary_filtration_lift X i k hi hlt s t a hfil
  have hbfirst : b ≫ (background.quotients.tower A).rho 1 k (by omega) =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
    rw [←(background.quotients.tower A).rho_comp hi hik,←Category.assoc,hb]
    exact ha
  let β := boundaryRepresentative X k s t b
  obtain ⟨z,hz⟩ := nu_first_label_exists X (s+k+1) (t+k) β
  have hp := first_label_lift_permanent X (s+k+1) (t+k) z β hz
  have hdz := adjacent_boundary_differential X k (by omega) s t x z b hbfirst hz
  have hzdet : Detects (background.convergence (.nu X)) (s+k+1,t+k,t+i)
      (nuWeightLabel background X (s+k+1) (t+k) (t+i) (by omega) z)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i))) := by
    rw [←hb]
    by_cases hik' : i=k
    · subst i
      simpa only [β,boundaryRepresentative,A,(background.quotients.tower A).rho_id,Category.comp_id] using
        nu_first_label_detects X (s+k+1) (t+k) z hp β hz
    have hlam := nu_lambda_detects X (k-i) (by omega) (s+k+1) (t+k) z hp β hz
    have hind : (s+k+1,t+k,(t+k)-(k-i:ℕ))=(s+k+1,t+k,t+i) :=
      Prod.ext rfl (Prod.ext rfl (by dsimp; omega))
    have hlam := detects_transport hind _ _ hlam
    convert hlam using 1
    · have transport (w w' : ℤ) (hw : w=w') (hw₁ : w≤t+k) (hw₂ : w'≤t+k)
          (h : (s+k+1,t+k,w)=(s+k+1,t+k,w')) :
          regradeE2 h (nuWeightLabel background X (s+k+1) (t+k) w hw₁ z) =
            nuWeightLabel background X (s+k+1) (t+k) w' hw₂ z := by subst w'; rfl
      exact (transport _ _ (by omega) _ _ hind).symm
    · rw [absolute_boundary_restriction]
      dsimp only [β,boundaryRepresentative]
      rw [lambda_regrade]
      simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
  have hcong := nu_detected_labels_congruent X (s+k+1) (t+k) (t+i) (by omega) y z _ hy hzdet
  have hboundary : y-z ∈ boundaries background X k (s+k+1,t+k) :=
    boundaries_monotone background X (s+k+1,t+k) (by omega) hcong
  exact (differentialAt_of_congruent background X
    (⟨by omega,hdz⟩ : DifferentialAt background X (k+1) (s,t) (s+k+1,t+k) x z)
    ⟨by omega,by simpa only [add_sub_cancel_right] using hboundary⟩).2

end
end KIP126.ProofTools.Internal.Leibniz
