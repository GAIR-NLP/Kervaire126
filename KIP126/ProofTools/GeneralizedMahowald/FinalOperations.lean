module
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.ConvergenceOperations
/-! Strict representative preimages for the Mahowald comparison. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem finite_top_extension_preimage
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : Ambient background X (s,t))
    (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f r n s t x y)
    (htop : (r:ℤ)-1 ≤ n-normalizedExponent background.classicalTower f+1)
    (b : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (r-1)))
    (hb : Detects (background.convergence (.quotient (r-1) (.nu Y)))
      (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)
      (finiteTargetForExtension background X Y f (r-1) n s t W.length_lower y)
      (homotopyRegrade (by dsimp; omega) rfl b)) :
    ∃ a : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary),
      a ≫ finiteExtensionMap background X Y f (r-1) = b ∧
      Detects (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f)))
        (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
        (finiteSourceForExtension background X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl a) := by
  let A := (SyntheticObject.quotient (r-1) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary
  let B := XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (r-1)
  let p := (t-s,t+normalizedExponent background.classicalTower f)
  obtain ⟨_,a,b',hab,hax,hby⟩ := (tower_extension_iff
    (background.convergentMap (.quotient (r-1) (extensionSourceObject background X Y f))
      (.quotient (r-1) (.nu Y)) (finiteExtensionMap background X Y f (r-1)))
    p s n W.source W.target).mp W.equation
  have ha := source_frame_detects
    (background.convergence (.quotient (r-1) (extensionSourceObject background X Y f))) p s W.source
    _ W.source_rep a hax
  have hb' := source_frame_detects
    (background.convergence (.quotient (r-1) (.nu Y))) p (s+n) W.target
    _ W.target_rep b' hby
  have hr := W.page_ge_two
  have heq := finite_top_detection_unique Y (r-1) (by omega)
    (s+n) ((t-s)+(s+n)) (t+normalizedExponent background.classicalTower f) (by omega)
    _ _ _ hb' hb
  have heq' : ((background.syntheticTower.filtration B).F (s+n) p).arrow b' = b := by
    have hinj (u v w : ℤ) (huv : u=v) :
        Function.Injective (homotopyRegrade huv (rfl : w=w) (X:=B)) := by
      subst v
      exact Function.injective_id
    exact hinj _ _ _ _ heq
  refine ⟨((background.syntheticTower.filtration A).F s p).arrow a, hab.trans heq', ha⟩

end
end KIP126.ProofTools.Internal.Mahowald
