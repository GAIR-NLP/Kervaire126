module

public import KIP126.ProofTools.LevelLanguage
public import KIP126.Literature.Standard.LambdaInversion
import all KIP126.ProofTools.FiniteLifting.CutoffDifferential
import all KIP126.ProofTools.FiniteLifting.LevelClassicalLift

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

public theorem cutoffAdamsDifferentialAtLevel
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
  exact KIP126.ProofTools.Internal.FiniteLifting.cutoffAdamsDifferentialAtLevel
    X Y f page level r m l s t κ x y u v hpage hpr hm hmUpper hl hu hv hdx
    hFinite hInfinity hκ hκD hsource hbottom hzero hzeroCrossing

public theorem finiteLevelExtensionToClassical
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (hx : IsPermanentCycle (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (he : KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page level m s t x y)
    (hnc : KIP126.ProofTools.Standard.LevelFiniteNoCrossing X Y f page level m s t) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+m,t+m) y ∧
      ∃ a : HomotopyGroup (t-s) (X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence X) (s,t) x a ∧
        ClassicalDetects (background.classicalConvergence Y) (s+m,t+m) y
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+m)-(s+m)=t-s by omega)) ≫ a ≫ f) := by
  exact KIP126.ProofTools.Internal.FiniteLifting.finiteLevelExtensionToClassical
    KIP126.Literature.Standard.realizationData
    KIP126.Literature.Standard.lambdaInversionAdamsComparison
    X Y f page level m s t x y hx he hnc

end
end KIP126.ProofTools.Standard
