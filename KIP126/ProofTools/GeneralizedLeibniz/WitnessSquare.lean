module
import all KIP126.ProofTools.GeneralizedLeibniz.SquareRepresentatives
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta

/-! Witness-level assembly for AimPaper Theorem 6.1. The finite witness
supplies the top edge; the actual lambda-propagated infinite witness supplies
the bottom edge. All degree transports use the GL bottom point.
The construction takes the specified left-edge and crossing comparisons
as hypotheses. -/

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
set_option maxHeartbeats 2400000

-- Witness-level specialization begins here.
private def glBottomSource (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    ((background.family.obj ((SyntheticObject.shift (1,-((page-1:ℕ):ℤ))
      (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).sequence.ssData
      (s+r,(t-s)+(s+r),t+normalizedExponent background.classicalTower f)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((background.family.obj ((SyntheticObject.shift (1,-((page-1:ℕ):ℤ))
      (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (gl_bottom_point page r s t (normalizedExponent background.classicalTower f) hpage hpr)))
      (lambdaBoundaryInfinity (extensionSourceObject background X Y f) (r-page).toNat (page-1)
        ((t+r-1)-(s+r),(t+r-1)+normalizedExponent background.classicalTower f) (s+r) W.source)

private def glBottomTarget (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    ((background.family.obj ((SyntheticObject.shift (1,-((page-1:ℕ):ℤ)) (.nu Y)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+r+l,(t-s)+(s+r+l),t+normalizedExponent background.classicalTower f)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((background.family.obj ((SyntheticObject.shift (1,-((page-1:ℕ):ℤ)) (.nu Y)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+r+l,p.1+(s+r+l),p.2)).eInfty)
    (gl_bottom_point page r s t (normalizedExponent background.classicalTower f) hpage hpr)))
      (lambdaBoundaryInfinity (.nu Y) (r-page).toNat (page-1)
        ((t+r-1)-(s+r),(t+r-1)+normalizedExponent background.classicalTower f) (s+r+l) W.target)

private theorem gl_bottom_extension (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    TowerExtensionEquation
      (background.convergentMap
        (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page-1:ℕ):ℤ))).map (background.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent background.classicalTower f) (s+r) l
      (glBottomSource X Y f page r l s t hpage hpr W)
      (glBottomTarget X Y f page r l s t hpage hpr W) := by
  obtain ⟨hbottom,_,_⟩ := infinite_extension_lambda_boundary_shift X Y f
    (r-page).toNat (page-1) l (s+r) (t+r-1) xInfinity yInfinity W
  let A := SyntheticObject.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f)
  let B := SyntheticObject.shift (1,-((page-1:ℕ):ℤ)) (.nu Y)
  let g := (SyntheticCategory.biShift (1,-((page-1:ℕ):ℤ))).map (background.normalizedMap X Y f).map
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
  exact transport _ _ (gl_bottom_point page r s t (normalizedExponent background.classicalTower f) hpage hpr)
    _ _ hbottom

private theorem gl_witness_square_high_filtration (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (r m l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {x : Ambient background X (s,t)} {y : Ambient background Y (s+m,t+m)}
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (WFinite : FiniteExtensionWitness background X Y f page m s t x y)
    (WInfinity : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hleft : TowerExtensionEquation
      (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (absoluteBoundary ((extensionSourceObject background X Y f).obj background.nu background.auxiliary) (page-1)))
      (t-s,t+normalizedExponent background.classicalTower f) s r WFinite.source
      (glBottomSource X Y f page r l s t hpage hpr WInfinity))
    (hsourceCrossing :
      TowerNoCrossing (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (absoluteBoundary ((extensionSourceObject background X Y f).obj background.nu background.auxiliary) (page-1)))
        (t-s,t+normalizedExponent background.classicalTower f) s r ∨
      TowerNoCrossing (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap background X Y f (page-1)))
        (t-s,t+normalizedExponent background.classicalTower f) s m)
    (hbottomCrossing : TowerNoCrossing
      (background.convergentMap (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page-1:ℕ):ℤ))).map (background.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent background.classicalTower f) (s+r) l) :
    ∃ aRight : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (page-1)),
      Detects (background.convergence (.quotient (page-1) (.nu Y)))
        (s+m,(t-s)+(s+m),t+normalizedExponent background.classicalTower f)
        (finiteTargetForExtension background X Y f (page-1) m s t WFinite.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl aRight) ∧
      FiltrationAtLeast background.syntheticTower (s+r+l)
        (biSuspensionHomEquiv (t-s) (t+normalizedExponent background.classicalTower f) (page-1:ℕ)
          (background.nu.functor.obj (Y.obj background.auxiliary)) (aRight ≫ XModLambdaN.proj _ (page-1))) := by
  exact absolute_boundary_square_high_filtration
    (extensionSourceObject background X Y f) (.nu Y) (background.normalizedMap X Y f).map
    (page-1) (t-s,t+normalizedExponent background.classicalTower f) s m r l
    WFinite.source WFinite.target
    (glBottomSource X Y f page r l s t hpage hpr WInfinity)
    (glBottomTarget X Y f page r l s t hpage hpr WInfinity)
    hleft WFinite.equation (gl_bottom_extension X Y f page r l s t hpage hpr WInfinity)
    hsourceCrossing hbottomCrossing _ WFinite.target_rep

private theorem gl_witness_square_detects (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (r m l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {x : Ambient background X (s,t)} {y : Ambient background Y (s+m,t+m)}
    {xInfinity : Ambient background X (s+r,t+r-1)}
    {yInfinity : Ambient background Y (s+r+l,t+r-1+l)}
    (WFinite : FiniteExtensionWitness background X Y f page m s t x y)
    (WInfinity : InfiniteExtensionWitness background X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hleft : TowerExtensionEquation
      (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (absoluteBoundary ((extensionSourceObject background X Y f).obj background.nu background.auxiliary) (page-1)))
      (t-s,t+normalizedExponent background.classicalTower f) s r WFinite.source
      (glBottomSource X Y f page r l s t hpage hpr WInfinity))
    (hsourceCrossing :
      TowerNoCrossing (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (absoluteBoundary ((extensionSourceObject background X Y f).obj background.nu background.auxiliary) (page-1)))
        (t-s,t+normalizedExponent background.classicalTower f) s r ∨
      TowerNoCrossing (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap background X Y f (page-1)))
        (t-s,t+normalizedExponent background.classicalTower f) s m)
    (hbottomCrossing : TowerNoCrossing
      (background.convergentMap (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page-1:ℕ):ℤ))).map (background.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent background.classicalTower f) (s+r) l)
    (target : (background.family.nu background.nu (Y.obj background.auxiliary)).E₂
      (s+r+l,(t-s)-1+(s+r+l),t+normalizedExponent background.classicalTower f+(page-1:ℕ)))
    (htarget : HasInfinityRepresentative _ 2
      (s+r+l,(t-s)+(s+r+l),t+normalizedExponent background.classicalTower f)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-((page-1:ℕ):ℤ))).page (.nu Y) 2 (by decide)
          ((t-s)-1,t+normalizedExponent background.classicalTower f+(page-1:ℕ)) (s+r+l)).hom target))
      (glBottomTarget X Y f page r l s t hpage hpr WInfinity)) :
    ∃ aRight : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (page-1)),
      Detects (background.convergence (.quotient (page-1) (.nu Y)))
        (s+m,(t-s)+(s+m),t+normalizedExponent background.classicalTower f)
        (finiteTargetForExtension background X Y f (page-1) m s t WFinite.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl aRight) ∧
      Detects (background.convergence (.nu Y))
        (s+r+l,(t-s)-1+(s+r+l),t+normalizedExponent background.classicalTower f+(page-1:ℕ)) target
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) (t+normalizedExponent background.classicalTower f) (page-1:ℕ)
            (background.nu.functor.obj (Y.obj background.auxiliary)) (aRight ≫ XModLambdaN.proj _ (page-1)))) := by
  exact absolute_boundary_square_detects_unshifted
    (extensionSourceObject background X Y f) (.nu Y) (background.normalizedMap X Y f).map
    (page-1) (t-s,t+normalizedExponent background.classicalTower f) s m r l
    WFinite.source WFinite.target
    (glBottomSource X Y f page r l s t hpage hpr WInfinity)
    (glBottomTarget X Y f page r l s t hpage hpr WInfinity)
    hleft WFinite.equation (gl_bottom_extension X Y f page r l s t hpage hpr WInfinity)
    hsourceCrossing hbottomCrossing _ WFinite.target_rep target htarget

end
end KIP126.ProofTools.Internal.Leibniz
