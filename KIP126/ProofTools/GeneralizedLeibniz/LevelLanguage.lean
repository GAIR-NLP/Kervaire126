module

import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.ProofTools.GeneralizedLeibniz.Square

/-! Level-indexed language for AimPaper's GL square.
The classical page is `page`, the source lambda level is `level`, and the
quotient exponent is `page + level - 1`. Crossing is tested in this quotient
at the fixed weight, using the shifted native source label.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def levelFiniteTargetLabel (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q level : ℕ) (m s t : ℤ)
    (hm : (normalizedExponent background.classicalTower f : ℤ) ≤ m)
    (y : Ambient background Y (s+m,t+m)) :
    (background.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
      background.nu background.auxiliary)).E₂
      (s+m,(t-s)+(s+m),t+normalizedExponent background.classicalTower f-level) :=
  regradeE2 (by ext <;> dsimp; omega)
    ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap
      2 (s+m,t+m,t+normalizedExponent background.classicalTower f-level)
      (nuWeightLabel background Y (s+m) (t+m)
        (t+normalizedExponent background.classicalTower f-level) (by omega) y))

private structure LevelFiniteExtensionWitness (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m)) where
  page_ge_two : 2 ≤ page
  length_lower : (normalizedExponent background.classicalTower f : ℤ) ≤ m
  length_upper : m ≤ (page:ℤ)-2+normalizedExponent background.classicalTower f
  source : ((background.family.obj ((SyntheticObject.quotient (page+level-1)
    (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f-level)).eInfty
  target : ((background.family.obj ((SyntheticObject.quotient (page+level-1) (.nu Y)).obj
    background.nu background.auxiliary)).sequence.ssData
      (s+m,(t-s)+(s+m),t+normalizedExponent background.classicalTower f-level)).eInfty
  source_rep : HasInfinityRepresentative _ 2 _
    (levelFiniteSourceLabel X (page+level-1) (normalizedExponent background.classicalTower f)
      s t level x) source
  target_rep : HasInfinityRepresentative _ 2 _
    (levelFiniteTargetLabel X Y f (page+level-1) level m s t length_lower y) target
  equation : TowerExtensionEquation
    (background.convergentMap (.quotient (page+level-1) (extensionSourceObject background X Y f))
      (.quotient (page+level-1) (.nu Y)) (finiteExtensionMap background X Y f (page+level-1)))
    (t-s,t+normalizedExponent background.classicalTower f-level) s m source target

private def LevelFiniteExtension (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m)) : Prop :=
  Nonempty (LevelFiniteExtensionWitness X Y f page level m s t x y)

private def LevelFiniteNoCrossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (m s t : ℤ) : Prop :=
  TowerNoCrossing (background.convergentMap
    (.quotient (page+level-1) (extensionSourceObject background X Y f))
    (.quotient (page+level-1) (.nu Y)) (finiteExtensionMap background X Y f (page+level-1)))
    (t-s,t+normalizedExponent background.classicalTower f-level) s m

private def LevelBoundaryNoCrossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r s t : ℤ) : Prop :=
  TowerNoCrossing (background.convergentMap
    (.quotient (page+level-1) (extensionSourceObject background X Y f))
    (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
    (absoluteBoundary ((extensionSourceObject background X Y f).obj background.nu background.auxiliary)
      (page+level-1)))
    (t-s,t+normalizedExponent background.classicalTower f-level) s r

private def LevelBottomNoCrossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r l s t : ℤ) : Prop :=
  TowerNoCrossing (background.convergentMap
    (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
    (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
    ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map
      (background.normalizedMap X Y f).map))
    (t-s,t+normalizedExponent background.classicalTower f-level) (s+r) l

private theorem level_gl_bottom_point (page level : ℕ) (r s t e : ℤ)
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r) :
    lambdaBoundaryPoint (r-page).toNat (page+level-1)
      ((t+r-1)-(s+r),(t+r-1)+e) = (t-s,t+e-level) := by
  have hk : ((r-page).toNat:ℤ) = r-page := Int.toNat_of_nonneg (by omega)
  have hq : ((page+level-1:ℕ):ℤ) = (page:ℤ)+level-1 := by omega
  ext <;> dsimp [lambdaBoundaryPoint] <;> omega

private def levelGLBottomSource (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    ((background.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ))
      (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).sequence.ssData
      (s+r,(t-s)+(s+r),t+normalizedExponent background.classicalTower f-level)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((background.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ))
      (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (level_gl_bottom_point page level r s t (normalizedExponent background.classicalTower f) hpage hpr)))
      (lambdaBoundaryInfinity (extensionSourceObject background X Y f) (r-page).toNat (page+level-1)
        ((t+r-1)-(s+r),(t+r-1)+normalizedExponent background.classicalTower f) (s+r) W.source)

private def levelGLBottomTarget (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    ((background.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+r+l,(t-s)+(s+r+l),t+normalizedExponent background.classicalTower f-level)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((background.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+r+l,p.1+(s+r+l),p.2)).eInfty)
    (level_gl_bottom_point page level r s t (normalizedExponent background.classicalTower f) hpage hpr)))
      (lambdaBoundaryInfinity (.nu Y) (r-page).toNat (page+level-1)
        ((t+r-1)-(s+r),(t+r-1)+normalizedExponent background.classicalTower f) (s+r+l) W.target)

private theorem level_gl_bottom_extension (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    TowerExtensionEquation
      (background.convergentMap
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map (background.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent background.classicalTower f-level) (s+r) l
      (levelGLBottomSource X Y f page level r l s t hpage hpr W)
      (levelGLBottomTarget X Y f page level r l s t hpage hpr W) := by
  obtain ⟨hbottom,_,_⟩ := infinite_extension_lambda_boundary_shift X Y f
    (r-page).toNat (page+level-1) l (s+r) (t+r-1) xInfinity yInfinity W
  let A := SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject background X Y f)
  let B := SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y)
  let g := (SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map (background.normalizedMap X Y f).map
  have transport (p p' : ℤ×ℤ) (hp : p=p')
      (x : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
        (s+r,p.1+(s+r),p.2)).eInfty)
      (y : ((background.family.obj (B.obj background.nu background.auxiliary)).sequence.ssData
        (s+r+l,p.1+(s+r+l),p.2)).eInfty)
      (he : TowerExtensionEquation (background.convergentMap A B g) p (s+r) l x y) :
      TowerExtensionEquation (background.convergentMap A B g) p' (s+r) l
        ((eqToHom (congrArg (fun p : ℤ×ℤ => ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
          (s+r,p.1+(s+r),p.2)).eInfty) hp)) x)
        ((eqToHom (congrArg (fun p : ℤ×ℤ => ((background.family.obj (B.obj background.nu background.auxiliary)).sequence.ssData
          (s+r+l,p.1+(s+r+l),p.2)).eInfty) hp)) y) := by
    subst p'
    exact he
  exact transport _ _ (level_gl_bottom_point page level r s t (normalizedExponent background.classicalTower f) hpage hpr)
    _ _ hbottom

end
end KIP126.ProofTools.Internal.Leibniz
