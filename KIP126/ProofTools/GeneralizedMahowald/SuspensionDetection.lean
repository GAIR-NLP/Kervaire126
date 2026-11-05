module
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionTarget
import all KIP126.ProofTools.GeneralizedLeibniz.DivisionLabels
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaShift
import KIP126.AdamsSynthetic
/-! Suspension of finite-quotient detecting representatives. First-quotient
compatibility determines the bottom layer. At positive lambda layers,
the BHS bottom representative differs by one higher filtration,
a bound preserved by unshifting. -/
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
set_option maxHeartbeats 2000000

private theorem quotient_unshift_preserves_filtration
    (X : AdamsObject (coefficients := background.coefficients)) (δ p : ℤ × ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (s : ℤ)
    (a : BiHom (p+δ).1 (p+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (quotientUnshift X δ p q ε a) := by
  let E := (essShift δ).filtered (.quotient q (.nu X)) p
  have hv := map_preserves_filtration
    (background.convergentMap (.quotient q (.shift δ (.nu X)))
      (.shift δ (.quotient q (.nu X))) ε.hom) (p+δ) s a ha
  obtain ⟨b,hb⟩ := filtration_representative_exists background.syntheticTower _ (p+δ) s
    (a ≫ ε.hom) hv
  have he : E.ambient.hom (quotientUnshift X δ p q ε a) = a ≫ ε.hom := by
    rw [(essShift δ).ambient_eq]
    have h := congrArg (fun z => z ≫ ε.hom) (shift_quotient_unshift X δ p q ε a)
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using h
  have hi : E.ambient.inv (a ≫ ε.hom) = quotientUnshift X δ p q ε a := by
    rw [←he]
    exact E.ambient.toLinearEquiv.symm_apply_apply _
  have hc := ConcreteCategory.congr_hom (E.symm.level_arrow s) b
  change ((background.syntheticTower.filtration _).F s p).arrow ((E.level s).inv b) =
    E.ambient.inv (((background.syntheticTower.filtration _).F s (p+δ)).arrow b) at hc
  erw [hb,hi] at hc
  have hm : quotientUnshift X δ p q ε a ∈ ModuleCat.subobjectModule _
      ((background.syntheticTower.filtration _).F s p) := ⟨(E.level s).inv b,hc⟩
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
    FiltrationAtLeast] using hm

private theorem detects_of_high_difference
    (A : SyntheticObject (coefficients := background.coefficients)) (p : Tridegree)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ p)
    (a b : BiHom (p.2.1-p.1) p.2.2 (A.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence A) p x a)
    (hd : FiltrationAtLeast background.syntheticTower (p.1+1) (b-a)) :
    Detects (background.convergence A) p x b := by
  have hd' := background.syntheticTower.filtrationSubmodule_antitone
    (A.obj background.nu background.auxiliary) (p.2.1-p.1,p.2.2) (show p.1 ≤ p.1+1 by omega) hd
  obtain ⟨d,hd⟩ := filtration_representative_exists background.syntheticTower _
    (p.2.1-p.1,p.2.2) p.1 (b-a) hd'
  have hz : Detects (background.convergence A) p 0 (b-a) := by
    refine ⟨0,HasInfinityRepresentative.zero _ 2 (by omega) p,d,hd,?_⟩
    rw [map_zero]
    symm
    apply ((background.syntheticTower.filtration _).toAssociatedGraded_eq_zero_iff _ _ _).mpr
    rw [hd]
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using ‹FiltrationAtLeast background.syntheticTower (p.1+1) (b-a)›
  simpa only [add_zero,add_sub_cancel] using detects_add (background.convergence A) p ha hz

private theorem quotient_unshift_sub
    (X : AdamsObject (coefficients := background.coefficients)) (δ p : ℤ × ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (a b : BiHom (p+δ).1 (p+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
    quotientUnshift X δ p q ε (a-b) =
      quotientUnshift X δ p q ε a - quotientUnshift X δ p q ε b := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  simp [quotientUnshift,Functor.map_sub,Preadditive.comp_sub,Preadditive.sub_comp]


private theorem finite_detected_target_bottom_lift
    (X : AdamsObject (coefficients := background.coefficients)) (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X q s t k x) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)),
      b ≫ (background.quotients.tower _).rho 1 (q-k) (by omega) =
        firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  obtain ⟨e,he,_⟩ := ha
  have hlabel : nuWeightLabel background X s t (t-k) (by omega) x =
      targetNuLabel background X s t k x := by
    have hk' : (t-(t-k)).toNat = k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel background X s t a x) = targetNuLabel background X s t b x := by
      subst b
      rfl
    exact transport _ k hk' _
  have hh := KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
    s t (t-k) (by omega) x e
  rw [hlabel] at hh
  have hx : x ∈ cycles background X (q-k:ℕ) (s,t) := by
    have hx := (hh.mp he).1
    convert hx using 1
    congr 1
    omega
  obtain ⟨b,hb⟩ := (KIP126.Literature.Standard.finite_lift_criterion X (q-k) (by omega) s t x).mp
    ((isCycle_iff_reaches background X ((q-k:ℕ)+1) (by omega) (s,t) x).mp
      ⟨by omega,by simpa using hx⟩)
  let f : nuZero background X ⟶ background.nu.functor.obj (X.obj background.auxiliary) :=
    SyntheticCategory.biShift_zero.hom.app _
  refine ⟨b ≫ XModLambdaN.map f (q-k),?_⟩
  rw [Category.assoc,←(background.quotients.natural f).rho_naturality (by omega),←Category.assoc,hb]


private theorem homotopy_regrade_sub {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    {A : SyntheticSpectrum} (a b : BiHom m w A) :
    homotopyRegrade hm hw (a-b) = homotopyRegrade hm hw a - homotopyRegrade hm hw b := by
  subst m'; subst w'; rfl

private theorem homotopy_regrade_filtration {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    {A : SyntheticSpectrum} (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (homotopyRegrade hm hw a) := by
  subst m'; subst w'; exact ha

private theorem suspension_unshift_high_difference
    (X : AdamsObject (coefficients := background.coefficients)) (q k : ℕ) (s t : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (a b : BiHom ((t+1)-s) (t+1-k)
      (XModLambdaN (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) q))
    (hdiff : FiltrationAtLeast background.syntheticTower (s+1) (a-b)) :
    FiltrationAtLeast background.syntheticTower (s+1)
      (quotientUnshift X (1,1) (t-s,t-k) q εq
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q)) -
       quotientUnshift X (1,1) (t-s,t-k) q εq
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (b ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q))) := by
  let f := XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q
  have hm := map_preserves_filtration
    (background.convergentMap (.quotient q (.nu (.shift 1 X))) (.quotient q (.shift (1,1) (.nu X))) f)
    ((t+1)-s,t+1-k) (s+1) _ hdiff
  have hr := homotopy_regrade_filtration
    (show (t+1)-s=((t-s,t-k)+(1,1)).1 by dsimp; omega)
    (show t+1-k=((t-s,t-k)+(1,1)).2 by dsimp; omega) (s+1) _ hm
  have hu := quotient_unshift_preserves_filtration X (1,1) (t-s,t-k) q εq (s+1) _ hr
  simp only [Preadditive.sub_comp,homotopy_regrade_sub] at hu
  erw [quotient_unshift_sub] at hu
  exact hu

private theorem suspension_finite_bottom_detects
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background X (s,t)) (sx : Ambient background (.shift 1 X) (s,t+1))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hε₁ : XModLambdaN.incl _ 1 ≫ ε₁.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hsx : (background.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x))
    (a : BiHom ((t+1)-s) (t+1)
      (XModLambdaN (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu (.shift 1 X)))) (s,t+1,t+1)
      (regradeE2 (by simp) (finiteTargetLabel background (.shift 1 X) q s (t+1) 0 sx)) a) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x))
      (quotientUnshift X (1,1) (t-s,t) q εq
        (homotopyRegrade (by dsimp; omega) rfl
          (a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q))) := by
  have ha' : Detects (background.convergence (.quotient q (.nu (.shift 1 X)))) (s,t+1,t+1-(0:ℕ))
      (finiteTargetLabel background (.shift 1 X) q s (t+1) 0 sx)
      (homotopyRegrade rfl (by simp) a) := by
    convert detects_transport (show (s,t+1,t+1)=(s,t+1,t+1-(0:ℕ)) by simp) _ _ ha using 1
    have inv {A : SyntheticAdamsSS} {i j : Tridegree} (h : i=j) (y : A.E₂ i) :
        regradeE2 h.symm (regradeE2 h y) = y := by subst j; rfl
    exact (inv _ _).symm
  obtain ⟨b,hb⟩ := finite_detected_target_bottom_lift (.shift 1 X) q 0 hq s (t+1) sx _ ha'
  simp only [Nat.sub_zero] at b hb
  have hbX := suspension_finite_target_desuspend X q hq s t x sx ε₁ εq hε₁ hεq hsx b hb
  have hbS := first_label_detects_unshifted (.shift 1 X) q hq s (t+1) sx b hb
  have hd := detects_sub_filtration (background.convergence (.quotient q (.nu (.shift 1 X))))
    (s,t+1,t+1) ha hbS
  let f := XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q
  have hm := map_preserves_filtration
    (background.convergentMap (.quotient q (.nu (.shift 1 X))) (.quotient q (.shift (1,1) (.nu X))) f)
    ((t+1)-s,t+1) (s+1) _ hd
  have hr := homotopy_regrade_filtration
    (show (t+1)-s=((t-s,t)+(1,1)).1 by dsimp; omega) rfl (s+1) _ hm
  have hu := quotient_unshift_preserves_filtration X (1,1) (t-s,t) q εq (s+1) _ hr
  simp only [Preadditive.sub_comp,homotopy_regrade_sub] at hu
  erw [quotient_unshift_sub] at hu
  exact detects_of_high_difference (.quotient q (.nu X)) (s,t,t) _ _ _ hbX.2 hu


private theorem suspension_finite_positive_detects
    (X : AdamsObject (coefficients := background.coefficients)) (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (x : Ambient background X (s,t)) (sx : Ambient background (.shift 1 X) (s,t+1))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (εb : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (q-k) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hε₁ : XModLambdaN.incl _ 1 ≫ ε₁.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hεb : XModLambdaN.incl _ (q-k) ≫ εb.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (q-k)))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hsx : (background.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x))
    (a : BiHom ((t+1)-s) (t+1-k)
      (XModLambdaN (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu (.shift 1 X)))) (s,t+1,t+1-k)
      (finiteTargetLabel background (.shift 1 X) q s (t+1) k sx) a) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X q s t k x)
      (quotientUnshift X (1,1) (t-s,t-k) q εq
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q))) := by
  obtain ⟨b,hb⟩ := finite_detected_target_bottom_lift (.shift 1 X) q k hkq s (t+1) sx a ha
  have hbX := suspension_finite_target_desuspend X (q-k) (by omega) s t x sx
    ε₁ εb hε₁ hεb hsx b hb
  have hlX := Leibniz.finite_quotient_lambda_detects X q k hk hkq s t x _ hbX.1
  have hlS := Leibniz.finite_quotient_lambda_detects (.shift 1 X) q k hk hkq s (t+1) sx b hb
  have hdiff := detects_sub_filtration (background.convergence (.quotient q (.nu (.shift 1 X))))
    (s,t+1,t+1-k) ha hlS
  have hu := suspension_unshift_high_difference X q k s t εq _ _ hdiff
  rw [suspension_finite_lambda_unshift X q k hk hkq s t εb εq hεb hεq b] at hu
  exact detects_of_high_difference (.quotient q (.nu X)) (s,t,t-k) _ _ _ hlX hu

/-- Suspension detection in every finite lambda layer through
the specified quotient comparison. -/
private theorem suspension_finite_detects
    (X : AdamsObject (coefficients := background.coefficients)) (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient background X (s,t)) (sx : Ambient background (.shift 1 X) (s,t+1))
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hsx : (background.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x))
    (a : BiHom ((t+1)-s) (t+1-k)
      (XModLambdaN (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu (.shift 1 X)))) (s,t+1,t+1-k)
      (finiteTargetLabel background (.shift 1 X) q s (t+1) k sx) a) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X q s t k x)
      (quotientUnshift X (1,1) (t-s,t-k) q εq
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q))) := by
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) 1
    (background.nu.functor.obj (X.obj background.auxiliary))
  by_cases hk : k=0
  · subst k
    have ha0 := detects_transport (show (s,t+1,t+1-(0:ℕ))=(s,t+1,t+1) by simp) _ _ ha
    have h0 := suspension_finite_bottom_detects X q hkq s t x sx ε₁ εq hε₁ hεq hsx _ ha0
    have hback := detects_transport (show (s,t,t)=(s,t,t-(0:ℕ)) by simp) _ _ h0
    convert hback using 1
    · have inv {A : SyntheticAdamsSS} {i j : Tridegree} (h : i=j) (y : A.E₂ i) :
          regradeE2 h.symm (regradeE2 h y) = y := by subst j; rfl
      exact (inv _ _).symm
    · have unshift_weight (m w w' : ℤ) (hw : w=w')
          (b : BiHom ((m,w)+(1,1)).1 ((m,w)+(1,1)).2
            (XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
              (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
          homotopyRegrade rfl hw (quotientUnshift X (1,1) (m,w) q εq b) =
            quotientUnshift X (1,1) (m,w') q εq
              (homotopyRegrade rfl (congrArg (fun z => z+1) hw) b) := by
        subst w'; rfl
      have twice {A : SyntheticSpectrum} {m m' m'' w w' w'' : ℤ}
          (hm : m=m') (hm' : m'=m'') (hw : w=w') (hw' : w'=w'')
          (b : BiHom m w A) :
          homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
            homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
        subst m'; subst m''; subst w'; subst w''; rfl
      rw [unshift_weight]
      simp only [←regrade_comp,twice]


  · obtain ⟨εb,hεb,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) (q-k)
      (background.nu.functor.obj (X.obj background.auxiliary))
    exact suspension_finite_positive_detects X q k (by omega) hkq s t x sx ε₁ εb εq
      hε₁ hεb hεq hsx a ha


end
end KIP126.ProofTools.Internal.Mahowald
