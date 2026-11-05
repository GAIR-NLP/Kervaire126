module
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayActual

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/- The corrected May target uses the inclusion of the infinite normalized
source label. The finite-edge decoder uses finiteNuLabel. They are exactly
the same label; this bridge changes no representative or quotient length. -/
private theorem normalized_included_source_label
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (s t : ℤ) (x : Ambient background X (s,t)) :
    familyPageMap background.family
      (XModLambdaN.incl ((extensionSourceObject background X Y g).obj background.nu background.auxiliary) q)
      2 (s,t,t+normalizedExponent background.classicalTower g)
      (regradeE2 (by simp) (infiniteSourceForExtension background X Y g s t x)) =
    regradeE2 (by simp)
      (finiteNuLabel background X q (normalizedExponent background.classicalTower g) s t 0 x) := by
  unfold infiniteSourceForExtension finiteNuLabel
  rw [page_regrade]
  have trans {E : SyntheticAdamsSS} {p q r : Tridegree}
      (hpq : p=q) (hqr : q=r) (a : E.E₂ p) :
      regradeE2 hqr (regradeE2 hpq a)=regradeE2 (hpq.trans hqr) a := by
    subst q; subst r; rfl
  rw [trans]
  rfl

private theorem corrected_second_image_finite_label
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (s t : ℤ) (x : Ambient background X (s,t))
    (D : SyntheticObject (coefficients := background.coefficients))
    (J : XModLambdaN ((extensionSourceObject background X Y g).obj background.nu background.auxiliary) q ⟶
      D.obj background.nu background.auxiliary)
    (u : BiHom (t-s) (t+normalizedExponent background.classicalTower g)
      (D.obj background.nu background.auxiliary))
    (hu : Detects (background.convergence D) (s,t,t+normalizedExponent background.classicalTower g)
      (familyPageMap background.family J 2 (s,t,t+normalizedExponent background.classicalTower g)
        (familyPageMap background.family
          (XModLambdaN.incl ((extensionSourceObject background X Y g).obj background.nu background.auxiliary) q)
          2 (s,t,t+normalizedExponent background.classicalTower g)
          (regradeE2 (by simp) (infiniteSourceForExtension background X Y g s t x)))) u) :
    Detects (background.convergence D) (s,t,t+normalizedExponent background.classicalTower g)
      (familyPageMap background.family J 2 (s,t,t+normalizedExponent background.classicalTower g)
        (regradeE2 (by simp)
          (finiteNuLabel background X q (normalizedExponent background.classicalTower g) s t 0 x))) u := by
  rw [normalized_included_source_label] at hu
  exact hu

private theorem finite_edge_detection_source_length
    (X Y : AdamsObject (coefficients := background.coefficients)) (g : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (j q : ℕ) (hj : j=q) (s t : ℤ) (x : Ambient background X (s,t))
    (D : SyntheticObject (coefficients := background.coefficients))
    (J : XModLambdaN ((extensionSourceObject background X Y g).obj background.nu background.auxiliary) j ⟶
      D.obj background.nu background.auxiliary)
    (u : BiHom (t-s) (t+normalizedExponent background.classicalTower g)
      (D.obj background.nu background.auxiliary))
    (hu : Detects (background.convergence D) (s,t,t+normalizedExponent background.classicalTower g)
      (familyPageMap background.family (by simpa only [hj,extensionSourceObject,SyntheticObject.obj] using J) 2
        (s,t,t+normalizedExponent background.classicalTower g)
        (regradeE2 (by simp)
          (finiteNuLabel background X q (normalizedExponent background.classicalTower g) s t 0 x))) u) :
    Detects (background.convergence D) (s,t,t+normalizedExponent background.classicalTower g)
      (familyPageMap background.family J 2 (s,t,t+normalizedExponent background.classicalTower g)
        (regradeE2 (by simp)
          (finiteNuLabel background X j (normalizedExponent background.classicalTower g) s t 0 x))) u := by
  subst j
  exact hu

private theorem finite_native_bottom_detection_reindex_exists
    (X : AdamsObject (coefficients := background.coefficients)) (q j : ℕ) (hj : q=j) (e s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t+e)
      ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj background.nu background.auxiliary))
    (ha : Detects (background.convergence (.quotient q (.shift (0,e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel background X q e s t 0 x)) a) :
    ∃ a' : BiHom (t-s) (t+e)
        ((SyntheticObject.quotient j (.shift (0,e) (.nu X))).obj background.nu background.auxiliary),
      Detects (background.convergence (.quotient j (.shift (0,e) (.nu X)))) (s,t,t+e)
        (regradeE2 (by simp) (finiteNuLabel background X j e s t 0 x)) a' := by
  subst j
  exact ⟨a,ha⟩

end
end KIP126.ProofTools.Internal.Mahowald
