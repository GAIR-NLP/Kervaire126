module

import all KIP126.Main.Internal.Moore.ConstructionCrossing

/-! Restriction and nonzero leading filtration of the actual Moore source.
At coefficient zero the finite infinity window has denominator B₁ = 0.
Thus a nonzero classical source cannot disappear into higher filtration. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem moore_finite_target_restriction_detection
    (X : AdamsObject (coefficients := background.coefficients))
    (i N k : ℕ) (hiN : i ≤ N) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X N s t k x) a) :
    Detects (background.convergence (.quotient i (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X i s t k x)
      (a ≫ (background.quotients.tower _).rho i N hiN) := by
  let ρ := (background.quotients.tower
    (background.nu.functor.obj (X.obj background.auxiliary))).rho i N hiN
  have hlabel : familyPageMap background.family ρ 2 (s,t,t-k)
      (finiteTargetLabel background X N s t k x) =
      finiteTargetLabel background X i s t k x := by
    unfold finiteTargetLabel
    change familyPageMap background.family ρ 2 (s,t,t-k)
      (familyPageMap background.family (XModLambdaN.incl _ N) 2 (s,t,t-k) _) = _
    rw [←ModuleCat.comp_apply,family_page_comp]
    rw [(background.quotients.tower _).rho_quotient]
    rfl
  have hdet := detects_map (.quotient N (.nu X)) (.quotient i (.nu X)) ρ
    (s,t,t-k) _ a ha
  erw [hlabel] at hdet
  exact hdet

private theorem moore_higher_filtration_has_zero_infinity
    (A : SyntheticObject (coefficients := background.coefficients)) (p : Tridegree)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ p)
    (a : BiHom (p.2.1-p.1) p.2.2 (A.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence A) p x a)
    (hhigh : FiltrationAtLeast background.syntheticTower (p.1+1) a) :
    HasInfinityRepresentative _ 2 p x 0 := by
  obtain ⟨e,he,a',ha',hgr⟩ := ha
  have hgr0 : (background.syntheticTower.filtration _).toAssociatedGraded p.1
      (p.2.1-p.1,p.2.2) a' = 0 := by
    apply ((background.syntheticTower.filtration _).toAssociatedGraded_eq_zero_iff _ _ _).mpr
    rw [ha']
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hhigh
  have he0 : e = 0 := by
    apply ((background.convergence A).identification p).toLinearEquiv.injective
    change ((background.convergence A).identification p).hom e =
      ((background.convergence A).identification p).hom 0
    rw [map_zero,hgr,hgr0]
  simpa only [he0] using he

/-- At weight t, the finite infinity denominator is the zero
submodule B₁, so a nonzero E₂ label cannot detect a higher-filtration class. -/
private theorem moore_finite_bottom_detection_not_high
    (X : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) (hx : x ≠ 0)
    (a : BiHom (t-s) (t-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-(0:ℕ))
      (finiteTargetLabel background X q s t 0 x) a) :
    ¬ FiltrationAtLeast background.syntheticTower (s+1) a := by
  intro hhigh
  have he := moore_higher_filtration_has_zero_infinity (.quotient q (.nu X))
    (s,t,t-(0:ℕ)) (finiteTargetLabel background X q s t 0 x) a ha hhigh
  have hlabel : nuWeightLabel background X s t (t-(0:ℕ)) (by omega) x =
      targetNuLabel background X s t 0 x := by
    have hk : (t-(t-(0:ℕ))).toNat = 0 := by omega
    have transport (k k' : ℕ) (h : k = k') (hp : (s,t,t-k) = (s,t,t-k')) :
        regradeE2 hp (targetNuLabel background X s t k x) =
          targetNuLabel background X s t k' x := by
      subst k'
      rfl
    exact transport _ 0 hk _
  have he' : HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q)
      2 (s,t,t-(0:ℕ))
      ((background.family.quotientProjection
        (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
        2 (s,t,t-(0:ℕ)) (nuWeightLabel background X s t (t-(0:ℕ)) (by omega) x)) 0 := by
    rw [hlabel]
    exact he
  obtain ⟨hc,hc0⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X q hq
    s t (t-(0:ℕ)) (by constructor <;> omega) x 0).mp he'
  rw [map_zero] at hc0
  have hb := (moore_subquotient_zero_iff _ _ ⟨x,hc⟩).mp hc0.symm
  apply hx
  simpa only [Nat.cast_zero,sub_zero,add_sub_cancel_right,boundaries_one,Submodule.mem_bot] using hb

/-- The same actual fourth-quotient representative restricts to the same
classical source label in the second quotient. -/
private theorem moore_source_second_restriction_detects
    (x : KIP126.AdamsComputation.Moore.Page 8 132)
    (c4 : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (hc4 : Detects (background.convergence
      (.quotient 4 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (8,132,132)
      (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 4 8 132 0 x) c4) :
    Detects (background.convergence
      (.quotient 2 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (8,132,132)
      (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 2 8 132 0 x)
      (c4 ≫ (background.quotients.tower
        (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 2 4 (by decide)) :=
  moore_finite_target_restriction_detection
    KIP126.AdamsComputation.Moore.adamsObject 2 4 0 (by decide) 8 132 x c4 hc4

/-- The source is essential in grade 8 after the second restriction,
using `B₁ = 0`. -/
private theorem moore_source_second_restriction_not_high
    (x : KIP126.AdamsComputation.Moore.Page 8 132) (hx : x ≠ 0)
    (c4 : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (hc4 : Detects (background.convergence
      (.quotient 4 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (8,132,132)
      (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 4 8 132 0 x) c4) :
    ¬ FiltrationAtLeast background.syntheticTower 9
      (c4 ≫ (background.quotients.tower
        (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 2 4 (by decide)) :=
  moore_finite_bottom_detection_not_high KIP126.AdamsComputation.Moore.adamsObject
    2 (by decide) 8 132 x hx _ (moore_source_second_restriction_detects x c4 hc4)

end
end KIP126.Main.Internal.Moore
end
