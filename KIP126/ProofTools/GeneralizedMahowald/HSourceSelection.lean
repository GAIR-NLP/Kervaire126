module
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import all KIP126.ProofTools.GeneralizedMahowald.Synchronization
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
set_option maxHeartbeats 2200000

private theorem finite_extension_source_sync_positive
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f r n s t x y)
    (he : normalizedExponent background.classicalTower f = 1)
    (hnc : NoCrossingOn background X ((r-1:ℕ)+q) r (s,t))
    (aZ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)))
    (haZ : Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) aZ) :
    ∃ ah : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
        ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary),
      Detects (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f)))
        (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
        (finiteSourceForExtension background X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl ah) ∧
      Detects (background.convergence (.quotient (r-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)
        (finiteTargetForExtension background X Y f (r-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl (ah≫finiteExtensionMap background X Y f (r-1))) ∧
      ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) (r-1) ≅
        (SyntheticCategory.biShift (0,1)).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)),
        XModLambdaN.incl _ (r-1)≫ε.hom =
          (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (r-1)) ∧
        ∃ a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)),
          Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
            (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) a₀ ∧
          a₀ ≫ ((background.quotients.tower _).triangle
            (show 0<r-1 by have := W.page_ge_two; omega)
            (show r-1<r-1+q by omega)).delta =
            aZ ≫ ((background.quotients.tower _).triangle
              (show 0<r-1 by have := W.page_ge_two; omega)
              (show r-1<r-1+q by omega)).delta ∧
          homotopyRegrade (show ((t-s,t)+(0,1)).1=t-s by simp)
            (show ((t-s,t)+(0,1)).2=t+1 by rfl) (shiftHomotopyClass (0,1) (t-s,t) a₀)≫ε.inv =
            ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
              (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
                (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)))
              (show (normalizedExponent background.classicalTower f : ℤ)=1 by omega)).mp ah) := by
  let p := (t-s,t+normalizedExponent background.classicalTower f)
  obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff _ p s n W.source W.target).mp W.equation
  let ah : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary) := ((background.syntheticTower.filtration
    ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).F s p).arrow ar
  have hsource := source_frame_detects
    (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f))) p s
    W.source _ W.source_rep ar hax
  have htarget := source_frame_detects (background.convergence (.quotient (r-1) (.nu Y))) p (s+n)
    W.target _ W.target_rep br hby
  rw [←hab] at htarget
  change Detects (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f)))
    (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
    (finiteSourceForExtension background X Y f (r-1) s t x)
    (homotopyRegrade (by dsimp; omega) rfl ah) at hsource
  have source_reindex (e : ℤ)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)))
      (ha : Detects (background.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,(t-s)+s,t+e) (regradeE2 (by simp) (finiteNuLabel background X (r-1) e s t 0 x))
        (homotopyRegrade (by dsimp; omega) rfl a)) :
      Detects (background.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel background X (r-1) e s t 0 x)) a := by
    have H := detects_transport
      (show (s,(t-s)+s,t+e)=(s,t,t+e) by congr 2; omega) _ _ ha
    have e2_comp {A : SyntheticAdamsSS} {u v w : Tridegree}
        (huv : u=v) (hvw : v=w) (z : A.E₂ u) :
        regradeE2 hvw (regradeE2 huv z)=regradeE2 (huv.trans hvw) z := by
      subst v; subst w; rfl
    have hcomp {m m' m'' w w' w'' : ℤ} {A : SyntheticSpectrum}
        (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
        (b : BiHom m w A) :
        homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
          homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
      subst m'; subst m''; subst w'; subst w''; rfl
    rw [e2_comp,hcomp] at H
    exact H
  have hs0 := source_reindex (normalizedExponent background.classicalTower f) ah hsource
  have heZ : (normalizedExponent background.classicalTower f : ℤ)=1 := by omega
  have cast_source (e : ℤ) (heZ : e=1)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)))
      (ha : Detects (background.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel background X (r-1) e s t 0 x)) a) :
      Detects (background.convergence (.quotient (r-1) (.shift (0,1) (.nu X))))
        (s,t,t+1) (regradeE2 (by simp) (finiteNuLabel background X (r-1) 1 s t 0 x))
        ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) (r-1))) heZ).mp a) := by
    subst e
    exact ha
  let ah1 : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)) := by
    exact ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) (r-1))) heZ).mp ah)
  have hsource1 : Detects (background.convergence (.quotient (r-1) (.shift (0,1) (.nu X))))
      (s,t,t+1) (regradeE2 (by simp) (finiteNuLabel background X (r-1) 1 s t 0 x)) ah1 := by
    exact cast_source _ heZ ah hs0
  obtain ⟨ε,hε,a₀,_,ha₀,hback⟩ := positive_finite_source_unshifted X (r-1)
    (by have := W.page_ge_two; omega) s t x ah1 hsource1
  have hnc' : NoCrossingOn background X ((r-1:ℕ)+q) ((r-1:ℕ)+1) (s,t) := by
    have hr := W.page_ge_two
    convert hnc using 1
    omega
  have hδ := relative_boundary_equal_of_no_crossing X (r-1) q
    (by have := W.page_ge_two; omega) hq s t hnc' a₀ aZ
    (detects_sub_filtration (background.convergence (.quotient (r-1) (.nu X))) (s,t,t) ha₀ haZ)
  exact ⟨ah,hsource,htarget,ε,hε,a₀,ha₀,hδ,hback⟩

private theorem finite_extension_source_sync_zero
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f r n s t x y)
    (he : normalizedExponent background.classicalTower f = 0)
    (hnc : NoCrossingOn background X ((r-1:ℕ)+q) r (s,t))
    (aZ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)))
    (haZ : Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) aZ) :
    ∃ ah : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
        ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary),
      Detects (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f)))
        (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
        (finiteSourceForExtension background X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl ah) ∧
      Detects (background.convergence (.quotient (r-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)
        (finiteTargetForExtension background X Y f (r-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl (ah≫finiteExtensionMap background X Y f (r-1))) ∧
      ∃ a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)),
          Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
            (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) a₀ ∧
          a₀ ≫ ((background.quotients.tower _).triangle
            (show 0<r-1 by have := W.page_ge_two; omega)
            (show r-1<r-1+q by omega)).delta =
            aZ ≫ ((background.quotients.tower _).triangle
              (show 0<r-1 by have := W.page_ge_two; omega)
              (show r-1<r-1+q by omega)).delta ∧
          homotopyRegrade rfl (show t=t+0 by simp) a₀≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) (r-1) =
            ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
              (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
                (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)))
              (show (normalizedExponent background.classicalTower f : ℤ)=0 by omega)).mp ah) := by
  let p := (t-s,t+normalizedExponent background.classicalTower f)
  obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff _ p s n W.source W.target).mp W.equation
  let ah : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary) := ((background.syntheticTower.filtration
    ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).F s p).arrow ar
  have hsource := source_frame_detects
    (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f))) p s
    W.source _ W.source_rep ar hax
  have htarget := source_frame_detects (background.convergence (.quotient (r-1) (.nu Y))) p (s+n)
    W.target _ W.target_rep br hby
  rw [←hab] at htarget
  change Detects (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f)))
    (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
    (finiteSourceForExtension background X Y f (r-1) s t x)
    (homotopyRegrade (by dsimp; omega) rfl ah) at hsource
  have source_reindex (e : ℤ)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)))
      (ha : Detects (background.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,(t-s)+s,t+e) (regradeE2 (by simp) (finiteNuLabel background X (r-1) e s t 0 x))
        (homotopyRegrade (by dsimp; omega) rfl a)) :
      Detects (background.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel background X (r-1) e s t 0 x)) a := by
    have H := detects_transport
      (show (s,(t-s)+s,t+e)=(s,t,t+e) by congr 2; omega) _ _ ha
    have e2_comp {A : SyntheticAdamsSS} {u v w : Tridegree}
        (huv : u=v) (hvw : v=w) (z : A.E₂ u) :
        regradeE2 hvw (regradeE2 huv z)=regradeE2 (huv.trans hvw) z := by
      subst v; subst w; rfl
    have hcomp {m m' m'' w w' w'' : ℤ} {A : SyntheticSpectrum}
        (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
        (b : BiHom m w A) :
        homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
          homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
      subst m'; subst m''; subst w'; subst w''; rfl
    rw [e2_comp,hcomp] at H
    exact H
  have hs0 := source_reindex (normalizedExponent background.classicalTower f) ah hsource
  have heZ : (normalizedExponent background.classicalTower f : ℤ)=0 := by omega
  have cast_source (e : ℤ) (heZ : e=0)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)))
      (ha : Detects (background.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel background X (r-1) e s t 0 x)) a) :
      Detects (background.convergence (.quotient (r-1) (.shift (0,0) (.nu X))))
        (s,t,t+0) (regradeE2 (by simp) (finiteNuLabel background X (r-1) 0 s t 0 x))
        ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) (r-1))) heZ).mp a) := by
    subst e
    exact ha
  let ah1 : BiHom (t-s) (t+0) (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) (r-1)) := by
    exact ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) (r-1))) heZ).mp ah)
  have hsource1 : Detects (background.convergence (.quotient (r-1) (.shift (0,0) (.nu X))))
      (s,t,t+0) (regradeE2 (by simp) (finiteNuLabel background X (r-1) 0 s t 0 x)) ah1 := by
    exact cast_source _ heZ ah hs0
  obtain ⟨a₀,_,ha₀,hback⟩ := zero_finite_source_unshifted X (r-1)
    (by have := W.page_ge_two; omega) s t x ah1 hsource1
  have hnc' : NoCrossingOn background X ((r-1:ℕ)+q) ((r-1:ℕ)+1) (s,t) := by
    have hr := W.page_ge_two
    convert hnc using 1
    omega
  have hδ := relative_boundary_equal_of_no_crossing X (r-1) q
    (by have := W.page_ge_two; omega) hq s t hnc' a₀ aZ
    (detects_sub_filtration (background.convergence (.quotient (r-1) (.nu X))) (s,t,t) ha₀ haZ)
  exact ⟨ah,hsource,htarget,a₀,ha₀,hδ,hback⟩

/- The inverse shift in the two normalized-exponent cases. -/
private def FiniteSourceUnshifts
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (k : ℕ) (s t : ℤ)
    (a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) k))
    (ah : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      ((SyntheticObject.quotient k (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)) : Prop :=
    (∃ he : normalizedExponent background.classicalTower f = 0,
      homotopyRegrade rfl (show t=t+0 by simp) a₀≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) k =
        ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
          (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
            (background.nu.functor.obj (X.obj background.auxiliary))) k))
          (show (normalizedExponent background.classicalTower f : ℤ)=0 by omega)).mp ah)) ∨
    (∃ he : normalizedExponent background.classicalTower f = 1,
      ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) k ≅
        (SyntheticCategory.biShift (0,1)).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) k),
        XModLambdaN.incl _ k≫ε.hom =
          (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ k) ∧
        homotopyRegrade (show ((t-s,t)+(0,1)).1=t-s by simp)
          (show ((t-s,t)+(0,1)).2=t+1 by rfl)
          (shiftHomotopyClass (0,1) (t-s,t) a₀)≫ε.inv =
          ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
            (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
              (background.nu.functor.obj (X.obj background.auxiliary))) k))
            (show (normalizedExponent background.classicalTower f : ℤ)=1 by omega)).mp ah))

private def FiniteExtensionAtSource
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f r n s t x y)
    (a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1))) : Prop :=
    ∃ ah : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
        ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary),
      Detects (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f)))
        (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
        (finiteSourceForExtension background X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl ah) ∧
      Detects (background.convergence (.quotient (r-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)
        (finiteTargetForExtension background X Y f (r-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl (ah≫finiteExtensionMap background X Y f (r-1))) ∧
      FiniteSourceUnshifts X Y f (r-1) s t a₀ ah

private theorem finite_extension_source_sync
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f r n s t x y)
    (hnc : NoCrossingOn background X ((r-1:ℕ)+q) r (s,t))
    (aZ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)))
    (haZ : Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) aZ) :
    ∃ a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)),
      Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) a₀ ∧
      a₀ ≫ ((background.quotients.tower _).triangle
        (show 0<r-1 by have := W.page_ge_two; omega)
        (show r-1<r-1+q by omega)).delta =
        aZ ≫ ((background.quotients.tower _).triangle
          (show 0<r-1 by have := W.page_ge_two; omega)
          (show r-1<r-1+q by omega)).delta ∧
      FiniteExtensionAtSource X Y f r n s t x y W a₀ := by
  by_cases he : normalizedExponent background.classicalTower f = 0
  · obtain ⟨ah,hs,ht,a₀,ha₀,hδ,hback⟩ :=
      finite_extension_source_sync_zero X Y f r q hq n s t x y W he hnc aZ haZ
    exact ⟨a₀,ha₀,hδ,ah,hs,ht,Or.inl ⟨he,hback⟩⟩
  · have he1 : normalizedExponent background.classicalTower f = 1 := by
      have := normalizedExponent_le_one background.classicalTower f
      omega
    obtain ⟨ah,hs,ht,ε,hε,a₀,ha₀,hδ,hback⟩ :=
      finite_extension_source_sync_positive X Y f r q hq n s t x y W he1 hnc aZ haZ
    exact ⟨a₀,ha₀,hδ,ah,hs,ht,Or.inr ⟨he1,ε,hε,hback⟩⟩

/- The selected source equals the original source outside the differential
no-crossing branch. The extension relation is conditional on that branch. -/
private theorem select_finite_extension_source
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f r n s t x y)
    (aZ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)))
    (haZ : Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) aZ) :
    ∃ a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (r-1)),
      Detects (background.convergence (.quotient (r-1) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel background X (r-1) s t 0 x)) a₀ ∧
      a₀ ≫ ((background.quotients.tower _).triangle
        (show 0<r-1 by have := W.page_ge_two; omega)
        (show r-1<r-1+q by omega)).delta =
        aZ ≫ ((background.quotients.tower _).triangle
          (show 0<r-1 by have := W.page_ge_two; omega)
          (show r-1<r-1+q by omega)).delta ∧
      (NoCrossingOn background X ((r-1:ℕ)+q) r (s,t) →
        FiniteExtensionAtSource X Y f r n s t x y W a₀) := by
  by_cases hnc : NoCrossingOn background X ((r-1:ℕ)+q) r (s,t)
  · obtain ⟨a₀,ha₀,hδ,hext⟩ := finite_extension_source_sync X Y f r q hq n s t x y W hnc aZ haZ
    exact ⟨a₀,ha₀,hδ,fun _ => hext⟩
  · exact ⟨aZ,haZ,rfl,fun h => (hnc h).elim⟩

end
end KIP126.ProofTools.Internal.Mahowald
