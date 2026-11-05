module
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import KIP126.AdamsSynthetic
/-! Finite bottom-weight target labels under classical suspension.
Uses the first-quotient suspension compatibility.
The weighted case with a positive λ exponent remains a separate step. -/
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

private theorem first_label_inline (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t)) :
    firstLabel background X s t x =
      homotopyRegrade rfl (by simp) ((background.firstQuotient X 0 s t).symm x) := by
  have cast (m w w' : ℤ) (h : w=w') (A : SyntheticSpectrum) (a : BiHom m w A) :
      homotopyRegrade rfl h a = (congrArg (fun v => BiHom m v A) h).mp a := by
    subst w'; rfl
  exact (cast _ _ _ _ _ _).symm

private theorem suspension_first_unshift
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t)) (sx : Ambient background (.shift 1 X) (s,t+1))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hsx : (background.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x)) :
    quotientUnshift X (1,1) (t-s,t) 1 ε
      (homotopyRegrade (by dsimp; omega) rfl
        ((firstLabel background (.shift 1 X) s (t+1) sx ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
          XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom 1)) =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hf := firstQuotient_suspension X s t x sx ε hε hsx
  rw [←first_label_inline,←first_label_inline] at hf
  have hc : homotopyRegrade (show (t+1)-s=((t-s,t)+(1,1)).1 by dsimp; omega) rfl
      ((firstLabel background (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
        XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom 1) =
      shiftHomotopyClass (1,1) (t-s,t)
        (firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫ ε.inv := by
    apply (cancel_mono ε.hom).mp
    rw [←regrade_comp,Category.assoc,hf,homotopy_regrade_inverse,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [hc,quotient_unshift_shift]

private theorem suspension_finite_target_desuspend
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
    (ha : a ≫ (background.quotients.tower _).rho 1 q hq =
      firstLabel background (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    let a₀ := quotientUnshift X (1,1) (t-s,t) q εq
      (homotopyRegrade (by dsimp; omega) rfl
        (a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q))
    a₀ ≫ (background.quotients.tower _).rho 1 q hq =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
    Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x)) a₀ := by
  dsimp only
  have hfirst : (a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q) ≫
      (background.quotients.tower _).rho 1 q hq =
      (firstLabel background (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
        XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom 1 := by
    rw [Category.assoc,←(background.quotients.natural
      (background.nu.suspensionIso (X.obj background.auxiliary)).hom).rho_naturality,
      ←Category.assoc]
    erw [ha]
  have h : quotientUnshift X (1,1) (t-s,t) q εq
      (homotopyRegrade (by dsimp; omega) rfl
        (a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q)) ≫
      (background.quotients.tower _).rho 1 q hq =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [quotient_unshift_restriction X (1,1) (t-s,t) 1 q (by decide) hq ε₁ εq hε₁ hεq,
      ←regrade_comp,hfirst,suspension_first_unshift X s t x sx ε₁ hε₁ hsx]
  exact ⟨h,first_label_detects_unshifted X q hq s t x _ h⟩

private theorem suspension_finite_target_unshifted
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background X (s,t)) (sx : Ambient background (.shift 1 X) (s,t+1))
    (hsx : (background.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x))
    (a : BiHom ((t+1)-s) (t+1)
      (XModLambdaN (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) q))
    (ha : a ≫ (background.quotients.tower _).rho 1 q hq =
      firstLabel background (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    ∃ (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
        (SyntheticCategory.biShift (1,1)).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)),
      XModLambdaN.incl _ q ≫ εq.hom =
        (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q) ∧
      ∃ a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
        a₀ ≫ (background.quotients.tower _).rho 1 q hq =
          firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
        Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x)) a₀ ∧
        homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass (1,1) (t-s,t) a₀) ≫ εq.inv =
          a ≫ XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom q := by
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) 1
    (background.nu.functor.obj (X.obj background.auxiliary))
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) q
    (background.nu.functor.obj (X.obj background.auxiliary))
  have h := suspension_finite_target_desuspend X q hq s t x sx ε₁ εq hε₁ hεq hsx a ha
  refine ⟨εq,hεq,_,h.1,h.2,?_⟩
  rw [←regrade_comp,shift_quotient_unshift,homotopy_regrade_inverse]

end
end KIP126.ProofTools.Internal.Mahowald
