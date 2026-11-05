module
import all KIP126.ProofTools.DetectionOperations
import KIP126.Literature
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedMahowald.Signs
import all KIP126.ProofTools.StretchingRepresentatives

/-! E₂ consequences of the finite g-extension in AimPaper Theorem 6.12.
At the bottom weight, the absence of incoming differentials lets the detected
associated grade determine the E₂ label. A positive-length extension has zero
leading image; a length-zero extension has the specified target as leading image. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- An E₂ label representing zero at infinity is zero when no differential enters. -/
private theorem infinity_zero_no_incoming (A : SyntheticAdamsSS) (p : Tridegree)
    (hin : ∀ r : ℤ, 2 ≤ r → A.sequence.d r (p-A.sequence.diffDeg r)=0)
    (x : A.E₂ p) (hx : HasInfinityRepresentative A 2 p x 0) : x=0 := by
  obtain ⟨_,z,hz,hz0⟩ := hx
  let D := A.sequence.ssData p
  let k : WithTop ℕ := ↑(2-A.sequence.r₀).toNat
  have hB : D.B ⊤ = D.B k := boundaries_top_eq_of_d_eq_zero A.sequence 2
    (by rw [A.firstPage]) p hin
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z _) z).mp hz0
  rw [hB] at hb
  rw [← hz]
  let z' := (Subobject.ofLE (D.Z ⊤) (D.Z k) (D.Z_anti le_top)) z
  change D.pageπ k z' = 0
  apply (subobject_cokernel_π_eq_zero_iff (D.B k) (D.Z k) (D.B_le_Z _) z').mpr
  change ((Subobject.ofLE (D.Z ⊤) (D.Z k) (D.Z_anti le_top)) ≫ (D.Z k).arrow) z ∈ _
  rwa [Subobject.ofLE_arrow]

/-- A representative lying one filtration higher has zero associated graded class. -/
private theorem detects_high_infinity_zero (A : SyntheticObject (coefficients := background.coefficients)) (p : Tridegree)
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
  have he0 : e=0 := by
    apply ((background.convergence A).identification p).toLinearEquiv.injective
    change ((background.convergence A).identification p).hom e =
      ((background.convergence A).identification p).hom 0
    rw [map_zero,hgr,hgr0]
  simpa only [he0] using he

/-- The bottom of a finite ν quotient has no incoming differentials. -/
private theorem finite_bottom_high_label_zero (Y : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q)
    (s t w : ℤ) (hw : t ≤ w)
    (x : (background.family.obj (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)).E₂ (s,t,w))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu Y))) (s,t,w) x a)
    (hhigh : FiltrationAtLeast background.syntheticTower (s+1) a) : x=0 := by
  apply infinity_zero_no_incoming _ (s,t,w) _ x
    (detects_high_infinity_zero (.quotient q (.nu Y)) (s,t,w) x a ha hhigh)
  intro r hr
  have hdeg : (s,t,w)-(background.family.obj
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)).sequence.diffDeg r =
      (s-r,t-r+1,w) := by
    change (s,t,w)-(background.family.functor.obj _).diffDeg r = _
    rw [background.family.differentialDegree]
    simp only [syntheticAdamsRawShift,Prod.mk_sub_mk,sub_zero]
    congr 2
    omega
  have hzero := KIP126.Literature.Standard.finite_quotient_vanishing Y q hq r hr
    (s-r) (t-r+1) w (Or.inl (by omega))
  have hzero' : IsZero ((background.family.obj
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)).Page r
      ((s,t,w)-(background.family.obj
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)).sequence.diffDeg r)) := by
    rw [hdeg]
    exact hzero
  exact hzero'.eq_of_src _ _

/-- Positive extension length forces the leading finite E₂ image to vanish. -/
private theorem finite_positive_extension_map_e2_zero
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (m s t : ℤ) (hm : 0<m)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (W : FiniteExtensionWitness background X Y g r m s t x y) :
    familyPageMap background.family (finiteExtensionMap background X Y g (r-1)) 2
      (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
      (finiteSourceForExtension background X Y g (r-1) s t x) = 0 := by
  let A := SyntheticObject.quotient (r-1) (extensionSourceObject background X Y g)
  let B := SyntheticObject.quotient (r-1) (.nu Y)
  let p := (t-s,t+normalizedExponent background.classicalTower g)
  obtain ⟨_,a,b,hab,hax,hby⟩ := (tower_extension_iff
    (background.convergentMap A B (finiteExtensionMap background X Y g (r-1)))
    p s m W.source W.target).mp W.equation
  have ha := source_frame_detects (background.convergence A) p s W.source
    _ W.source_rep a hax
  have hmap := detects_map A B (finiteExtensionMap background X Y g (r-1))
    (s,p.1+s,p.2) _ _ ha
  have hbfil : FiltrationAtLeast background.syntheticTower (s+m) (((background.syntheticTower.filtration
      (B.obj background.nu background.auxiliary)).F (s+m) p).arrow b) := by
    have hmem : (((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F (s+m) p).arrow b)
        ∈ ModuleCat.subobjectModule _ ((background.syntheticTower.filtration
          (B.obj background.nu background.auxiliary)).F (s+m) p) := ⟨b,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hmem
  have hhigh := background.syntheticTower.filtrationSubmodule_antitone
    (B.obj background.nu background.auxiliary) p (show s+1≤s+m by omega) hbfil
  have hhigh' : FiltrationAtLeast background.syntheticTower (s+1)
      ((homotopyRegrade (show p.1=(p.1+s)-s by omega) rfl
        (((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F s p).arrow a)) ≫
          finiteExtensionMap background X Y g (r-1)) := by
    have hcast (m m' w : ℤ) (he : m=m') (a : BiHom m w (A.obj background.nu background.auxiliary)) :
        homotopyRegrade he rfl a ≫ finiteExtensionMap background X Y g (r-1) =
          homotopyRegrade he rfl (a ≫ finiteExtensionMap background X Y g (r-1)) := by
      subst m'; rfl
    rw [hcast,hab]
    have hf (m m' w : ℤ) (he : m=m')
        (b : BiHom m w (B.obj background.nu background.auxiliary))
        (hb : FiltrationAtLeast background.syntheticTower (s+1) b) :
        FiltrationAtLeast background.syntheticTower (s+1) (homotopyRegrade he rfl b) := by
      subst m'; exact hb
    exact hf _ _ _ _ _ hhigh
  exact finite_bottom_high_label_zero Y (r-1) (by have := W.page_ge_two; omega)
    s (p.1+s) p.2 (by dsimp [p]; omega) _ _ hmap hhigh'


/-- The same vanishing before quotienting, by the retained E₂ window. -/
private theorem positive_extension_map_e2_zero
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (m s t : ℤ) (hm : 0<m)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (W : FiniteExtensionWitness background X Y g r m s t x y) :
    familyPageMap background.family (background.normalizedMap X Y g).map 2
      (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
      (infiniteSourceForExtension background X Y g s t x) = 0 := by
  let A := (extensionSourceObject background X Y g).obj background.nu background.auxiliary
  let B := background.nu.functor.obj (Y.obj background.auxiliary)
  let p : Tridegree := (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
  have hsource : finiteSourceForExtension background X Y g (r-1) s t x =
      familyPageMap background.family (XModLambdaN.incl A (r-1)) 2 p
        (infiniteSourceForExtension background X Y g s t x) := by
    unfold finiteSourceForExtension infiniteSourceForExtension finiteNuLabel
    rw [page_regrade]
    rfl
  have hfinite := finite_positive_extension_map_e2_zero X Y g r m s t hm x y W
  rw [hsource] at hfinite
  change familyPageMap background.family (XModLambdaN.map (background.normalizedMap X Y g).map (r-1)) 2 p
    (familyPageMap background.family (XModLambdaN.incl A (r-1)) 2 p
      (infiniteSourceForExtension background X Y g s t x))=0 at hfinite
  dsimp only [A,extensionSourceObject,SyntheticObject.obj] at hfinite
  rw [← ModuleCat.comp_apply,family_page_comp] at hfinite
  change familyPageMap background.family
    (XModLambdaN.incl A (r-1) ≫ XModLambdaN.map (background.normalizedMap X Y g).map (r-1)) 2 p
      (infiniteSourceForExtension background X Y g s t x)=0 at hfinite
  rw [←XModLambdaN.incl_naturality,←family_page_comp,ModuleCat.comp_apply] at hfinite
  by_cases he : normalizedExponent background.classicalTower g = 0
  · haveI : IsIso (familyPageMap background.family (XModLambdaN.incl B (r-1)) 2 p) := by
      exact KIP126.Literature.Standard.finite_quotient_retained Y (r-1)
        (by have := W.page_ge_two; omega) s ((t-s)+s) (t+normalizedExponent background.classicalTower g)
        (by have hr := W.page_ge_two; simp only [he,Nat.cast_zero,add_zero,sub_add_cancel,sub_self]; omega)
    apply (ModuleCat.mono_iff_injective
      (familyPageMap background.family (XModLambdaN.incl B (r-1)) 2 p)).mp inferInstance
    change familyPageMap background.family (XModLambdaN.incl B (r-1)) 2 p
      (familyPageMap background.family (background.normalizedMap X Y g).map 2 p
        (infiniteSourceForExtension background X Y g s t x)) =
      familyPageMap background.family (XModLambdaN.incl B (r-1)) 2 p 0
    rw [map_zero]
    exact hfinite
  · have hz := KIP126.Literature.Standard.above_diagonal Y 2 (by omega) s ((t-s)+s)
      (t+normalizedExponent background.classicalTower g) (by omega)
    exact ModuleCat.isZero_iff_subsingleton.mp hz |>.elim _ _


/-- The no-incoming argument survives a common shift of the finite quotient. -/
private theorem shifted_finite_bottom_high_label_zero
    (Y : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q) (δ p : ℤ × ℤ) (s : ℤ)
    (hw : p.1+s ≤ p.2)
    (x : (background.family.obj ((SyntheticObject.shift δ (.quotient q (.nu Y))).obj
      background.nu background.auxiliary)).E₂ (s,(p+δ).1+s,(p+δ).2))
    (a : BiHom ((p+δ).1+s-s) (p+δ).2
      ((SyntheticObject.shift δ (.quotient q (.nu Y))).obj background.nu background.auxiliary))
    (ha : Detects (background.convergence (.shift δ (.quotient q (.nu Y))))
      (s,(p+δ).1+s,(p+δ).2) x a)
    (hhigh : FiltrationAtLeast background.syntheticTower (s+1) a) : x=0 := by
  apply infinity_zero_no_incoming _ (s,(p+δ).1+s,(p+δ).2) _ x
    (detects_high_infinity_zero (.shift δ (.quotient q (.nu Y))) _ x a ha hhigh)
  intro r hr
  let Z := SyntheticObject.shift δ (.quotient q (.nu Y))
  have hdeg : (s,(p+δ).1+s,(p+δ).2)-
      (background.family.obj (Z.obj background.nu background.auxiliary)).sequence.diffDeg r =
      (s-r,((p.1+1,p.2)+δ).1+(s-r),((p.1+1,p.2)+δ).2) := by
    change (s,(p+δ).1+s,(p+δ).2)-(background.family.functor.obj _).diffDeg r = _
    rw [background.family.differentialDegree]
    simp only [syntheticAdamsRawShift,Prod.mk_sub_mk,sub_zero,Prod.fst_add,Prod.snd_add]
    congr 2; omega
  have hz := KIP126.Literature.Standard.finite_quotient_vanishing Y q hq r hr
    (s-r) ((p.1+1)+(s-r)) p.2 (Or.inl (by omega))
  let e := (essShift δ).page (.quotient q (.nu Y)) r hr (p.1+1,p.2) (s-r)
  have hzero := hz.of_iso e.symm
  have hzero' : IsZero ((background.family.obj (Z.obj background.nu background.auxiliary)).Page r
      ((s,(p+δ).1+s,(p+δ).2)-(background.family.obj (Z.obj background.nu background.auxiliary)).sequence.diffDeg r)) := by
    rw [hdeg]
    exact hzero
  exact hzero'.eq_of_src _ _

/-- Shift the actual representative and its filtration to prove finite E₂ vanishing. -/
private theorem finite_positive_extension_shifted_map_e2_zero
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (m s t : ℤ) (hm : 0<m) (δ : ℤ × ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (W : FiniteExtensionWitness background X Y g r m s t x y) :
    let A := SyntheticObject.quotient (r-1) (extensionSourceObject background X Y g)
    let p := (t-s,t+normalizedExponent background.classicalTower g)
    familyPageMap background.family ((SyntheticCategory.biShift δ).map
      (finiteExtensionMap background X Y g (r-1))) 2 (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page A 2 (by decide) p s).hom
        (finiteSourceForExtension background X Y g (r-1) s t x)) = 0 := by
  dsimp only
  let A := SyntheticObject.quotient (r-1) (extensionSourceObject background X Y g)
  let B := SyntheticObject.quotient (r-1) (.nu Y)
  let p := (t-s,t+normalizedExponent background.classicalTower g)
  let G := finiteExtensionMap background X Y g (r-1)
  obtain ⟨_,a,b,hab,hax,hby⟩ := (tower_extension_iff
    (background.convergentMap A B G) p s m W.source W.target).mp W.equation
  have ha := source_frame_detects (background.convergence A) p s W.source
    _ W.source_rep a hax
  have hmap := shifted_map_detects A (.shift δ B) δ p s
    ((SyntheticCategory.biShift δ).map G) _ _ ha
  obtain ⟨b',hb',_⟩ := shift_frame B δ p (s+m) W.target b hby
  have hbfil : FiltrationAtLeast background.syntheticTower (s+m)
      (shiftHomotopyClass δ p (((background.syntheticTower.filtration
        (B.obj background.nu background.auxiliary)).F (s+m) p).arrow b)) := by
    rw [←hb']
    have hmem : (((background.syntheticTower.filtration
        ((SyntheticObject.shift δ B).obj background.nu background.auxiliary)).F (s+m) (p+δ)).arrow b')
        ∈ ModuleCat.subobjectModule _ ((background.syntheticTower.filtration
          ((SyntheticObject.shift δ B).obj background.nu background.auxiliary)).F (s+m) (p+δ)) := ⟨b',rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast,SyntheticObject.obj,syntheticHomotopy] using hmem
  have hhigh := background.syntheticTower.filtrationSubmodule_antitone
    ((SyntheticObject.shift δ B).obj background.nu background.auxiliary) (p+δ) (show s+1≤s+m by omega) hbfil
  have heq : shiftHomotopyClass δ p
      (((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F s p).arrow a) ≫
        (SyntheticCategory.biShift δ).map G =
      shiftHomotopyClass δ p
        (((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F (s+m) p).arrow b) := by
    rw [←hab]
    simp only [shiftHomotopyClass,Functor.map_comp,Category.assoc]
  have hhigh' : FiltrationAtLeast background.syntheticTower (s+1)
      ((homotopyRegrade (show (p+δ).1=(p+δ).1+s-s by omega) rfl
        (shiftHomotopyClass δ p
          (((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F s p).arrow a))) ≫
            (SyntheticCategory.biShift δ).map G) := by
    rw [←regrade_comp,heq]
    have hf (m m' w : ℤ) (he : m=m')
        (b : BiHom m w ((SyntheticObject.shift δ B).obj background.nu background.auxiliary))
        (hb : FiltrationAtLeast background.syntheticTower (s+1) b) :
        FiltrationAtLeast background.syntheticTower (s+1) (homotopyRegrade he rfl b) := by
      subst m'; exact hb
    exact hf _ _ _ _ _ hhigh
  exact shifted_finite_bottom_high_label_zero Y (r-1)
    (by have := W.page_ge_two; omega) δ p s (by dsimp [p]; omega) _ _ hmap hhigh'


/-- Labels detecting the same bottom-weight representative agree at E₂. -/
private theorem finite_bottom_detects_label_unique (Y : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0<q) (s t w : ℤ) (hw : t≤w)
    (x y : (background.family.obj (XModLambdaN
      (background.nu.functor.obj (Y.obj background.auxiliary)) q)).E₂ (s,t,w))
    (a : BiHom (t-s) w (XModLambdaN
      (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (hx : Detects (background.convergence (.quotient q (.nu Y))) (s,t,w) x a)
    (hy : Detects (background.convergence (.quotient q (.nu Y))) (s,t,w) y a) : x=y := by
  have hsub := detects_add (background.convergence (.quotient q (.nu Y))) (s,t,w)
    hx (detects_neg hy)
  have hz : Detects (background.convergence (.quotient q (.nu Y))) (s,t,w) (x-y) 0 := by
    simpa only [←sub_eq_add_neg,sub_self] using hsub
  apply sub_eq_zero.mp
  apply finite_bottom_high_label_zero Y q hq s t w hw (x-y) 0 hz
  exact ⟨0,by simp⟩

/-- A zero-length finite extension has the specified target as its leading image. -/
private theorem finite_zero_extension_map_e2_target
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+0,t+0))
    (W : FiniteExtensionWitness background X Y g r 0 s t x y) :
    familyPageMap background.family (finiteExtensionMap background X Y g (r-1)) 2
      (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
      (finiteSourceForExtension background X Y g (r-1) s t x) =
      regradeE2 (by simp) (finiteTargetForExtension background X Y g (r-1) 0 s t W.length_lower y) := by
  let A := SyntheticObject.quotient (r-1) (extensionSourceObject background X Y g)
  let B := SyntheticObject.quotient (r-1) (.nu Y)
  let p := (t-s,t+normalizedExponent background.classicalTower g)
  obtain ⟨_,a,b,hab,hax,hby⟩ := (tower_extension_iff
    (background.convergentMap A B (finiteExtensionMap background X Y g (r-1)))
    p s 0 W.source W.target).mp W.equation
  have ha := source_frame_detects (background.convergence A) p s W.source
    _ W.source_rep a hax
  have hb := source_frame_detects (background.convergence B) p (s+0) W.target
    _ W.target_rep b hby
  have hmap := detects_map A B (finiteExtensionMap background X Y g (r-1))
    (s,p.1+s,p.2) _ _ ha
  have hcast (m m' w : ℤ) (he : m=m') (a : BiHom m w (A.obj background.nu background.auxiliary)) :
      homotopyRegrade he rfl a ≫ finiteExtensionMap background X Y g (r-1) =
        homotopyRegrade he rfl (a ≫ finiteExtensionMap background X Y g (r-1)) := by
    subst m'; rfl
  rw [hcast,hab] at hmap
  have hb' : Detects (background.convergence B) (s,p.1+s,p.2)
      (regradeE2 (by dsimp [p]; simp) (finiteTargetForExtension background X Y g (r-1) 0 s t W.length_lower y))
      (homotopyRegrade (show p.1=(p.1+s)-s by omega) rfl
        (((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F (s+0) p).arrow b)) := by
    have transport {j k : Tridegree} (he : j=k)
        (z : (background.family.obj (B.obj background.nu background.auxiliary)).E₂ j)
        {u w : ℤ} (b : BiHom u w (B.obj background.nu background.auxiliary))
        (hu : u=j.2.1-j.1) (hw : w=j.2.2)
        (hu' : u=k.2.1-k.1) (hw' : w=k.2.2)
        (h : Detects (background.convergence B) j z (homotopyRegrade hu hw b)) :
        Detects (background.convergence B) k (regradeE2 he z) (homotopyRegrade hu' hw' b) := by
      subst k
      exact h
    exact transport (by dsimp [p]; simp) _ _ _ _ _ _ hb
  exact finite_bottom_detects_label_unique Y (r-1) (by have := W.page_ge_two; omega)
    s (p.1+s) p.2 (by dsimp [p]; omega) _ _ _ hmap hb'

/-- Remove the quotient from the zero-length leading-image equation. -/
private theorem zero_extension_map_e2_target
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+0,t+0))
    (W : FiniteExtensionWitness background X Y g r 0 s t x y) :
    familyPageMap background.family (background.normalizedMap X Y g).map 2
      (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
      (infiniteSourceForExtension background X Y g s t x) =
      regradeE2 (by simp) (infiniteTargetForExtension background X Y g 0 s t W.length_lower y) := by
  let p := (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
  let V := background.nu.functor.obj (Y.obj background.auxiliary)
  have he : normalizedExponent background.classicalTower g = 0 := by
    have h := W.length_lower
    omega
  letI : IsIso ((background.family.quotientProjection V (r-1)).pageMap 2 p) :=
    KIP126.Literature.Standard.finite_quotient_retained Y (r-1)
      (by have := W.page_ge_two; omega) s ((t-s)+s) (t+normalizedExponent background.classicalTower g)
      (by have := W.page_ge_two; rw [he]; constructor <;> omega)
  apply (ModuleCat.mono_iff_injective ((background.family.quotientProjection V (r-1)).pageMap 2 p)).mp inferInstance
  have hf := finite_zero_extension_map_e2_target X Y g r s t x y W
  have source_comp : familyPageMap background.family
      (XModLambdaN.incl ((extensionSourceObject background X Y g).obj background.nu background.auxiliary) (r-1)) 2 p
      (infiniteSourceForExtension background X Y g s t x) = finiteSourceForExtension background X Y g (r-1) s t x := by
    unfold infiniteSourceForExtension finiteSourceForExtension finiteNuLabel
    rw [← page_regrade]
    rfl
  have target_comp : familyPageMap background.family (XModLambdaN.incl V (r-1)) 2 p
      (regradeE2 (by dsimp [p]; simp) (infiniteTargetForExtension background X Y g 0 s t W.length_lower y)) =
      regradeE2 (by dsimp [p]; simp) (finiteTargetForExtension background X Y g (r-1) 0 s t W.length_lower y) := by
    unfold infiniteTargetForExtension finiteTargetForExtension finiteTargetLabel
    simp only [← page_regrade]
    rfl
  change familyPageMap background.family (XModLambdaN.incl V (r-1)) 2 p
    (familyPageMap background.family (background.normalizedMap X Y g).map 2 p _) = _
  rw [←ModuleCat.comp_apply,family_page_comp,XModLambdaN.incl_naturality,
    ←family_page_comp,ModuleCat.comp_apply]
  erw [source_comp,target_comp]
  exact hf


/-- Express the zero-length leading image in the fixed unshifted bottom-weight coordinates. -/
private theorem zero_extension_map_e2_bottom_target
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+0,t+0))
    (W : FiniteExtensionWitness background X Y g r 0 s t x y) :
    familyPageMap background.family (background.normalizedMap X Y g).map 2 (s+0,t+0,t+0)
      (regradeE2 (by have := W.length_lower; ext <;> dsimp <;> omega)
        (infiniteSourceForExtension background X Y g s t x)) =
      nuWeightLabel background Y (s+0) (t+0) (t+0) (by omega) y := by
  have he : normalizedExponent background.classicalTower g=0 := by
    have := W.length_lower
    omega
  have hf := zero_extension_map_e2_target X Y g r s t x y W
  have hp : (s,(t-s)+s,t+normalizedExponent background.classicalTower g)=(s+0,t+0,t+0) := by
    rw [he]
    simp
  have H := congrArg (regradeE2 hp) hf
  rw [page_regrade] at H
  refine H.trans ?_
  have regrade_comp {E : SyntheticAdamsSS} {p₁ p₂ p₃ : Tridegree}
      (h₁ : p₁=p₂) (h₂ : p₂=p₃) (z : E.E₂ p₁) :
      regradeE2 h₂ (regradeE2 h₁ z) = regradeE2 (h₁.trans h₂) z := by
    subst p₂; subst p₃; rfl
  unfold infiniteTargetForExtension nuWeightLabel
  rw [regrade_comp,regrade_comp]
  have labels (k k' : ℕ) (hk : k=k') (p : Tridegree)
      (h₁ : (s+0,t+0,t+0-k)=p) (h₂ : (s+0,t+0,t+0-k')=p) :
      regradeE2 h₁ (targetNuLabel background Y (s+0) (t+0) k y) =
        regradeE2 h₂ (targetNuLabel background Y (s+0) (t+0) k' y) := by
    subst k'; rfl
  apply labels
  rw [he]
  simp

end
end KIP126.ProofTools.Internal.Mahowald
