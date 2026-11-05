module

import all KIP126.ProofTools.SyntheticProgramRules
import all KIP126.ProofTools.GeneralizedLeibniz.LevelGL

/-! Classical Adams differentials from the actual quotient boundary square
with a crossing cutoff. Both boundary labels are transported on the same
representative before the weighted reverse comparison is applied. -/

@[expose] section
namespace KIP126.ProofTools.Internal.FiniteLifting
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.ProgramRules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 2400000
set_option Elab.async false

private theorem boundary_extension_detects_unshifted
    (B : SyntheticObject (coefficients := background.coefficients)) (q : ℕ) (p : ℤ × ℤ) (s D v : ℤ) (hv : v=s+D)
    (y : ((background.family.obj ((SyntheticObject.quotient q B).obj background.nu background.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (w : ((background.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) B).obj background.nu background.auxiliary)).sequence.ssData
      (v,p.1+v,p.2)).eInfty)
    (he : TowerExtensionEquation
      (background.convergentMap (.quotient q B) (.shift (1,-(q:ℤ)) B)
        (absoluteBoundary (B.obj background.nu background.auxiliary) q)) p s D y
      ((eqToHom (congrArg (fun j => ((background.family.obj
        ((SyntheticObject.shift (1,-(q:ℤ)) B).obj background.nu background.auxiliary)).sequence.ssData
          (j,p.1+j,p.2)).eInfty) hv)) w))
    (y0 : (background.family.obj ((SyntheticObject.quotient q B).obj background.nu background.auxiliary)).E₂
      (s,p.1+s,p.2))
    (hy : HasInfinityRepresentative _ 2 (s,p.1+s,p.2) y0 y)
    (w0 : (background.family.obj (B.obj background.nu background.auxiliary)).E₂
      (v,p.1-1+v,p.2+q))
    (hw : HasInfinityRepresentative _ 2 (v,p.1+v,p.2)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-(q:ℤ))).page B 2 (by decide)
          (p.1-1,p.2+q) v).hom w0)) w) :
    ∃ a : BiHom p.1 p.2 ((SyntheticObject.quotient q B).obj background.nu background.auxiliary),
      Detects (background.convergence (.quotient q B)) (s,p.1+s,p.2) y0
        (homotopyRegrade (by dsimp; omega) rfl a) ∧
      Detects (background.convergence B) (v,p.1-1+v,p.2+q) w0
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv p.1 p.2 q (B.obj background.nu background.auxiliary)
            (a ≫ XModLambdaN.proj _ q))) := by
  subst v
  obtain ⟨_,ar,br,hab,har,hbr⟩ := (tower_extension_iff _ p s D y w).mp he
  have ha := source_frame_detects (background.convergence (.quotient q B)) p s y y0 hy ar har
  have hb := source_frame_detects (background.convergence (.shift (1,-(q:ℤ)) B))
    p (s+D) w _ hw br hbr
  rw [←hab] at hb
  exact ⟨_,ha,absolute_boundary_detects_unshifted B q p.1 p.2 (s+D) _ w0 hb⟩

/-- The complete Adams consequence of the actual four-edge cutoff square.
The zero extension starts at the target of this same finite top extension. -/
private theorem cutoff_adams_differential_at_level
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r m l s t κ : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (xInfinity : Ambient background X (s+r,t+r-1))
    (yInfinity : Ambient background Y (s+r+l,t+r-1+l))
    (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    (hm : (normalizedExponent background.classicalTower f:ℤ)≤m)
    (hmUpper : m≤(page:ℤ)-2+normalizedExponent background.classicalTower f)
    (hl : (normalizedExponent background.classicalTower f:ℤ)≤l)
    (hxInfinity : IsPermanent background X (s+r,t+r-1) xInfinity)
    (_hyInfinity : IsPermanent background Y (s+r+l,t+r-1+l) yInfinity)
    (hdx : DifferentialAt background X r (s,t) (s+r,t+r-1) x xInfinity)
    (WFinite : LevelFiniteExtensionWitness X Y f page level m s t x y)
    (WInfinity : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hκ : 1≤κ) (hκD : κ≤r+l-m)
    (hsourceCrossing : LevelBoundaryNoCrossing X Y f page level r s t ∨
      LevelFiniteNoCrossing X Y f page level m s t)
    (hbottomCrossing : EssentialNoCrossingRange
      (background.convergentMap
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map
          (background.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent background.classicalTower f-level) (s+r) l (s+m+κ))
    (hzero : TowerExtensionEquation
      (background.convergentMap (.quotient (page+level-1) (.nu Y))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
        (absoluteBoundary ((SyntheticObject.nu Y).obj background.nu background.auxiliary) (page+level-1)))
      (t-s,t+normalizedExponent background.classicalTower f-level) (s+m) (κ-1) WFinite.target 0)
    (hzeroCrossing : TowerNoCrossing
      (background.convergentMap (.quotient (page+level-1) (.nu Y))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
        (absoluteBoundary ((SyntheticObject.nu Y).obj background.nu background.auxiliary) (page+level-1)))
      (t-s,t+normalizedExponent background.classicalTower f-level) (s+m) (κ-1)) :
    DifferentialAt background Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y yInfinity := by
  let q : ℕ := page+level-1
  let K : ℕ := (r+l-m-1).toNat
  let d : ℕ := (m-normalizedExponent background.classicalTower f).toNat+level
  have hq : (q:ℤ)=(page:ℤ)+level-1 := by dsimp [q]; omega
  have hK : (K:ℤ)=r+l-m-1 := by dsimp [K]; omega
  have hd : (d:ℤ)=m-normalizedExponent background.classicalTower f+level := by
    dsimp [d]; omega
  have hdq : d<q := by omega
  have hqK : q-d≤K := by omega
  have hindex : (s+r+l,t+r-1+l)=(s+m+(K:ℤ)+1,t+m+(K:ℤ)) := by
    ext <;> omega
  let yExpected : Ambient background Y (s+m+(K:ℤ)+1,t+m+(K:ℤ)) :=
    (eqToHom (congrArg (fun p => Ambient background Y p) hindex)) yInfinity
  have hweight : t+normalizedExponent background.classicalTower f-level=t+m-d := by omega
  have htargetPoint :
      (s+m+(K:ℤ)+1,t+m+(K:ℤ),t+m-d+(q:ℤ)) =
      (s+r+l,(t-s)-1+(s+r+l),t+normalizedExponent background.classicalTower f-level+(q:ℤ)) := by
    ext <;> dsimp <;> omega
  let bottomLabel := regradeE2 htargetPoint
    (nuWeightLabel background Y (s+m+(K:ℤ)+1) (t+m+(K:ℤ))
      (t+m-d+(q:ℤ)) (by omega) yExpected)
  have hbottomLabel := level_gl_bottom_target_representative X Y f page level r l s t
    hpage hpr WInfinity bottomLabel (by
      apply (regradeE2_heq htargetPoint _).trans
      exact nuWeight_label_heq Y
        (s+m+(K:ℤ)+1) (t+m+(K:ℤ)) (t+m-d+(q:ℤ))
        (s+r+l) (t+r-1+l)
        (t+normalizedExponent background.classicalTower f-level+(page+level-1:ℕ))
        (by omega) (by omega) (by omega) (by omega) (by omega)
        yExpected yInfinity (eqToHom_apply_heq _ yInfinity))
  have hleft := level_gl_left_edge X Y f page level r m l s t
    hpage hpr hdx.2 hxInfinity WFinite WInfinity
  have hright := quotientBoundaryCutoff
    (extensionSourceObject background X Y f) (.nu Y) (background.normalizedMap X Y f).map q
    (t-s,t+normalizedExponent background.classicalTower f-level) s m r l κ
    (by omega) (by omega) (by omega) (by omega) hκD
    WFinite.source WFinite.target
    (levelGLBottomSource X Y f page level r l s t hpage hpr WInfinity)
    (levelGLBottomTarget X Y f page level r l s t hpage hpr WInfinity)
    WFinite.equation hleft
    (level_gl_bottom_extension X Y f page level r l s t hpage hpr WInfinity)
    (hsourceCrossing.elim Or.inr Or.inl) hbottomCrossing hzero hzeroCrossing
  obtain ⟨aRight,haRight,hboundary⟩ := boundary_extension_detects_unshifted (.nu Y) q
    (t-s,t+normalizedExponent background.classicalTower f-level) (s+m) (r+l-m)
    (s+r+l) (by omega) WFinite.target
    (levelGLBottomTarget X Y f page level r l s t hpage hpr WInfinity)
    hright _ WFinite.target_rep bottomLabel hbottomLabel
  have hstem : t-s=(t+m)-(s+m) := by omega
  let a := homotopyRegrade hstem hweight aRight
  have ha : Detects (background.convergence (.quotient q (.nu Y))) (s+m,t+m,t+m-d)
      ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap
        2 (s+m,t+m,t+m-d)
        (nuWeightLabel background Y (s+m) (t+m) (t+m-d) (by omega) y)) a := by
    have hp : (s+m,(t-s)+(s+m),t+normalizedExponent background.classicalTower f-level) =
        (s+m,t+m,t+normalizedExponent background.classicalTower f-level) := by
      ext <;> dsimp
      omega
    have hh := detects_transport hp _ _ haRight
    have weight_transport (w w' : ℤ) (hw : w=w') (hwt : w≤t+m) (hwt' : w'≤t+m)
        (a0 : BiHom ((t+m)-(s+m)) w
          (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
        (ha0 : Detects (background.convergence (.quotient q (.nu Y))) (s+m,t+m,w)
          ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap
            2 (s+m,t+m,w) (nuWeightLabel background Y (s+m) (t+m) w hwt y)) a0) :
        Detects (background.convergence (.quotient q (.nu Y))) (s+m,t+m,w')
          ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap
            2 (s+m,t+m,w') (nuWeightLabel background Y (s+m) (t+m) w' hwt' y))
          (homotopyRegrade rfl hw a0) := by
      subst w'
      exact ha0
    have hh' : Detects (background.convergence (.quotient q (.nu Y)))
        (s+m,t+m,t+normalizedExponent background.classicalTower f-level)
        ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap
          2 (s+m,t+m,t+normalizedExponent background.classicalTower f-level)
          (nuWeightLabel background Y (s+m) (t+m)
            (t+normalizedExponent background.classicalTower f-level) (by omega) y))
        (homotopyRegrade hstem rfl aRight) := by
      convert hh using 1
      · simp only [levelFiniteTargetLabel,normalized_regrade_trans]
        rfl
      · simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
    have hfinal := weight_transport _ _ hweight (by omega) (by omega) _ hh'
    convert hfinal using 1
    simp only [a,regrade_precomp,←Category.assoc,eqToHom_trans]
  have hboundary' : Detects (background.convergence (.nu Y))
      (s+m+(K:ℤ)+1,t+m+(K:ℤ),t+m-d+(q:ℤ))
      (nuWeightLabel background Y (s+m+(K:ℤ)+1) (t+m+(K:ℤ))
        (t+m-d+(q:ℤ)) (by omega) yExpected)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv ((t+m)-(s+m)) (t+m-d) q
          (background.nu.functor.obj (Y.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ q))) := by
    have hh := detects_transport htargetPoint.symm _ _ hboundary
    have boundary_regrade (m0 m1 w0 w1 : ℤ) (hm0 : m0=m1) (hw0 : w0=w1)
        (a0 : BiHom m0 w0 (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
        biSuspensionHomEquiv m1 w1 (q:ℤ) _
          (homotopyRegrade hm0 hw0 a0 ≫ XModLambdaN.proj _ q) =
        homotopyRegrade (congrArg (fun z => z-1) hm0)
          (congrArg (fun z : ℤ => z+(q:ℤ)) hw0)
          (biSuspensionHomEquiv m0 w0 (q:ℤ) _ (a0 ≫ XModLambdaN.proj _ q)) := by
      subst m1; subst w1; rfl
    convert hh using 1
    · simp only [bottomLabel,normalized_regrade_trans]
      rfl
    · dsimp only [a]
      dsimp only [SyntheticObject.obj]
      rw [boundary_regrade]
      simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
  have hresult : DifferentialAt background Y ((K:ℤ)+1)
      (s+m,t+m) (s+m+(K:ℤ)+1,t+m+(K:ℤ)) y yExpected :=
    ⟨by omega, finite_detected_boundary_differential_weighted Y q K d hdq hqK
      (s+m) (t+m) y yExpected a ha hboundary'⟩
  have hpageResult : (K:ℤ)+1=r+l-m := by omega
  rw [hpageResult] at hresult
  have undo_transport {p₁ p₂ : ℤ×ℤ} (hp : p₁=p₂)
      (z : Ambient background Y p₁)
      (h : DifferentialAt background Y (r+l-m) (s+m,t+m) p₂ y
        ((eqToHom (congrArg (fun p => Ambient background Y p) hp)) z)) :
      DifferentialAt background Y (r+l-m) (s+m,t+m) p₁ y z := by
    subst p₂
    exact h
  exact undo_transport hindex yInfinity hresult

/-- A finite-extension differential criterion with explicit crossing ranges.
The specified target label uniquely identifies the right-edge source,
even when that class is zero. -/
private theorem cutoffAdamsDifferentialAtLevel
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r m l s t κ : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (u : Ambient background X (s+r,t+r-1))
    (v : Ambient background Y (s+r+l,t+r-1+l))
    (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    (hm : (normalizedExponent background.classicalTower f:ℤ)≤m)
    (hmUpper : m≤(page:ℤ)-2+normalizedExponent background.classicalTower f)
    (hl : (normalizedExponent background.classicalTower f:ℤ)≤l)
    (hu : IsPermanent background X (s+r,t+r-1) u)
    (hv : IsPermanent background Y (s+r+l,t+r-1+l) v)
    (hdx : DifferentialAt background X r (s,t) (s+r,t+r-1) x u)
    (hFinite : KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page level m s t x y)
    (hInfinity : InfiniteExtension background X Y f l (s+r) (t+r-1) u v)
    (hκ : 1≤κ) (hκD : κ≤r+l-m)
    (hsource : KIP126.ProofTools.Standard.LevelBoundaryNoCrossing X Y f page level r s t ∨
      KIP126.ProofTools.Standard.LevelFiniteNoCrossing X Y f page level m s t)
    (hbottom : ∀ a c : ℤ, s+r<a → a≤c → s+m+κ≤c → c≤s+r+l →
      ∀ source target, ¬ TowerEssentialExtension
        (background.convergentMap
          (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
          (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
          ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map
            (background.normalizedMap X Y f).map))
        (t-s,t+normalizedExponent background.classicalTower f-level) a (c-a) source target)
    (hzero : ∃ η : ((background.family.obj ((SyntheticObject.quotient (page+level-1) (.nu Y)).obj
        background.nu background.auxiliary)).sequence.ssData
          (s+m,(t-s)+(s+m),t+normalizedExponent background.classicalTower f-level)).eInfty,
      HasInfinityRepresentative _ 2 _
        (regradeE2 (by ext <;> dsimp; omega)
          ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary))
            (page+level-1)).pageMap 2
            (s+m,t+m,t+normalizedExponent background.classicalTower f-level)
            (nuWeightLabel background Y (s+m) (t+m)
              (t+normalizedExponent background.classicalTower f-level) (by omega) y))) η ∧
      TowerExtensionEquation
        (background.convergentMap (.quotient (page+level-1) (.nu Y))
          (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
          (XModLambdaN.proj ((SyntheticObject.nu Y).obj background.nu background.auxiliary) (page+level-1) ≫
            (biSuspensionIso ((page+level-1:ℕ):ℤ)
              ((SyntheticObject.nu Y).obj background.nu background.auxiliary)).inv))
        (t-s,t+normalizedExponent background.classicalTower f-level) (s+m) (κ-1) η 0)
    (hzeroCrossing : ∀ a c : ℤ, s+m<a → a≤c → c≤s+m+(κ-1) →
      ∀ source target, ¬ TowerEssentialExtension
        (background.convergentMap (.quotient (page+level-1) (.nu Y))
          (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
          (XModLambdaN.proj ((SyntheticObject.nu Y).obj background.nu background.auxiliary) (page+level-1) ≫
            (biSuspensionIso ((page+level-1:ℕ):ℤ)
              ((SyntheticObject.nu Y).obj background.nu background.auxiliary)).inv))
        (t-s,t+normalizedExponent background.classicalTower f-level) a (c-a) source target) :
    DifferentialAt background Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y v := by
  obtain ⟨WFinite⟩ :=
    (KIP126.ProofTools.Standard.levelFiniteExtension_iff_internal X Y f page level m s t x y).mp hFinite
  obtain ⟨WInfinity⟩ := hInfinity
  obtain ⟨η,hη,hzero⟩ := hzero
  have hηeq : WFinite.target=η := WFinite.target_rep.unique hη
  rw [←hηeq] at hzero
  exact cutoff_adams_differential_at_level X Y f page level r m l s t κ x y u v
    hpage hpr hm hmUpper hl hu hv hdx WFinite WInfinity hκ hκD
    (hsource.imp
      (KIP126.ProofTools.Standard.levelBoundaryNoCrossing_iff_internal X Y f page level r s t).mp
      (KIP126.ProofTools.Standard.levelFiniteNoCrossing_iff_internal X Y f page level m s t).mp)
    hbottom hzero hzeroCrossing

end
end KIP126.ProofTools.Internal.FiniteLifting
