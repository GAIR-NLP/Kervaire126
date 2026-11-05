module

public import KIP126.ProofTools.Language
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.StretchingRepresentatives

/-! Naturality in AimPaper Proposition 6.20 on the domain of Definition 5.4. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal
noncomputable section

private theorem extension_square_map
    (A B A' B' : SyntheticObject (coefficients := background.coefficients))
    (g : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (g' : A'.obj background.nu background.auxiliary ⟶ B'.obj background.nu background.auxiliary)
    (ra : A.obj background.nu background.auxiliary ⟶ A'.obj background.nu background.auxiliary)
    (rb : B.obj background.nu background.auxiliary ⟶ B'.obj background.nu background.auxiliary)
    (hsquare : ra ≫ g' = g ≫ rb) (p : ℤ × ℤ) (s n : ℤ)
    (x : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((background.family.obj (B.obj background.nu background.auxiliary)).sequence.ssData
      (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation (background.convergentMap A B g) p s n x y) :
    TowerExtensionEquation (background.convergentMap A' B' g') p s n
      ((background.family.functor.map ra).eInftyMap (s,p.1+s,p.2) x)
      ((background.family.functor.map rb).eInftyMap (s+n,p.1+(s+n),p.2) y) := by
  obtain ⟨hn,a,b,hab,ha,hb⟩ :=
    (tower_extension_iff (background.convergentMap A B g) p s n x y).mp h
  let a' := ((background.convergentMap A A' ra).filteredMap.compat s p).choose a
  let b' := ((background.convergentMap B B' rb).filteredMap.compat (s+n) p).choose b
  have ha' : ((background.syntheticTower.filtration (A'.obj background.nu background.auxiliary)).F s p).arrow a' =
      ((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F s p).arrow a ≫ ra := by
    have hh := ConcreteCategory.congr_hom
      ((background.convergentMap A A' ra).filteredMap.compat s p).choose_spec a
    change _ = (background.convergentMap A A' ra).filteredMap.map p
      (((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F s p).arrow a) at hh
    exact hh.trans (ConcreteCategory.congr_hom
      ((background.convergentMap A A' ra).filteredMap_map p) _)
  have hb' : ((background.syntheticTower.filtration (B'.obj background.nu background.auxiliary)).F (s+n) p).arrow b' =
      ((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F (s+n) p).arrow b ≫ rb := by
    have hh := ConcreteCategory.congr_hom
      ((background.convergentMap B B' rb).filteredMap.compat (s+n) p).choose_spec b
    change _ = (background.convergentMap B B' rb).filteredMap.map p
      (((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F (s+n) p).arrow b) at hh
    exact hh.trans (ConcreteCategory.congr_hom
      ((background.convergentMap B B' rb).filteredMap_map p) _)
  apply (tower_extension_iff (background.convergentMap A' B' g') p s n _ _).mpr
  refine ⟨hn,a',b',?_,?_,?_⟩
  · rw [ha',hb',Category.assoc,hsquare,← Category.assoc,hab]
  · have hh := representative_grade_naturality
      (background.convergentMap A A' ra) p s a a' ha'.symm
    rw [ha] at hh
    have hc := (infinityGradedIso (background.convergence A) p s).toLinearEquiv.symm_apply_apply x
    change (infinityGradedIso (background.convergence A) p s).inv
      ((infinityGradedIso (background.convergence A) p s).hom x) = x at hc
    rw [hc] at hh
    exact ((infinityGradedIso (background.convergence A') p s).toLinearEquiv.apply_symm_apply _).symm.trans
      (congrArg (infinityGradedIso (background.convergence A') p s).hom hh)
  · have hh := representative_grade_naturality
      (background.convergentMap B B' rb) p (s+n) b b' hb'.symm
    rw [hb] at hh
    have hc := (infinityGradedIso (background.convergence B) p (s+n)).toLinearEquiv.symm_apply_apply y
    change (infinityGradedIso (background.convergence B) p (s+n)).inv
      ((infinityGradedIso (background.convergence B) p (s+n)).hom y) = y at hc
    rw [hc] at hh
    exact ((infinityGradedIso (background.convergence B') p (s+n)).toLinearEquiv.apply_symm_apply _).symm.trans
      (congrArg (infinityGradedIso (background.convergence B') p (s+n)).hom hh)

/-- Finite page extensions descend along the actual quotient reduction,
provided the target page belongs to the defining length range. This is the
naturality assertion of Proposition 6.20 on the domain of Definition 5.4. -/
public theorem finiteExtension_descends
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hnUpper : n ≤ (rEarlier : ℤ) - 2 + normalizedExponent background.classicalTower f)
    (h : FiniteExtension background X Y f rLater n s t x y) :
    FiniteExtension background X Y f rEarlier n s t x y := by
  obtain ⟨W⟩ := h
  let ra := (background.quotients.tower
    ((extensionSourceObject background X Y f).obj background.nu background.auxiliary)).rho
      (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  let rb := (background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).rho
    (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  refine ⟨{
    page_ge_two := hr
    length_lower := W.length_lower
    length_upper := hnUpper
    source_cycle := reaches_earlier (by omega) (by omega) W.source_cycle
    target_cycle := reaches_earlier (by omega) (by omega) W.target_cycle
    source := (background.family.functor.map ra).eInftyMap
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f) W.source
    target := (background.family.functor.map rb).eInftyMap
      (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f) W.target
    source_rep := ?_
    target_rep := ?_
    equation := ?_ }⟩
  · have hh := family_infinity_representative_map ra _ _ W.source W.source_rep
    rw [finite_source_rho] at hh
    exact hh
  · have hh := family_infinity_representative_map rb _ _ W.target W.target_rep
    rw [finite_target_rho] at hh
    exact hh
  · exact extension_square_map
      (.quotient (rLater-1) (extensionSourceObject background X Y f))
      (.quotient (rLater-1) (.nu Y))
      (.quotient (rEarlier-1) (extensionSourceObject background X Y f))
      (.quotient (rEarlier-1) (.nu Y))
      (finiteExtensionMap background X Y f (rLater-1))
      (finiteExtensionMap background X Y f (rEarlier-1)) ra rb
      ((background.quotients.natural (background.normalizedMap X Y f).map).rho_naturality
        (Nat.sub_le_sub_right hle 1))
      (t-s,t+normalizedExponent background.classicalTower f) s n W.source W.target W.equation

end
end KIP126.ProofTools.Paper
