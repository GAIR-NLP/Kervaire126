module

public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.GeneralizedLeibniz.LevelDivision

/-! Division by a positive lambda power in a finite quotient square.
The crossing condition excludes smaller-quotient essential extensions
whose target is killed by lambda below the requested filtration,
including the initial source filtration. Division constructs the smaller
source while preserving the specified source and image. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed
noncomputable section

/-- The extra no-crossing condition for division by `lambda^i` in quotient
`q`: every essential smaller-quotient extension with `s+i ≤ u ≤ v < N`
has target surviving the actual lambda map on E∞. All classes are at the
fixed stem/weight `(t-s, t+e(f))`, including the same-source row `u=s+i`. -/
public def FiniteLambdaKernelNoCrossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) : Prop :=
  ∀ u v : ℤ, s+i ≤ u → u ≤ v → v < N → ∀ source target,
    TowerEssentialExtension
      (background.convergentMap
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (extensionSourceObject background X Y f)))
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu Y)))
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (finiteExtensionMap background X Y f (q-i))))
      (t-s,t+normalizedExponent background.classicalTower f) u (v-u) source target →
      (background.family.functor.map
        ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).triangle
          hi hiq).lambdaMap).eInftyMap
        (u+(v-u),(t-s)+(u+(v-u)),t+normalizedExponent background.classicalTower f) target ≠ 0

/-- Divide a finite-quotient source by `lambda^i`, retaining its source
and image equations and reflecting target filtration. The crossing condition
is imposed below `N`; the construction determines the final preimage. -/
public theorem finiteLambdaDivision
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) (hsN : s+i ≤ N)
    (hcross : FiniteLambdaKernelNoCrossing X Y f q i hi hiq s t N)
    (a : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      (XModLambdaN ((extensionSourceObject background X Y f).obj background.nu background.auxiliary) q))
    (ha : FiltrationAtLeast background.syntheticTower (s+i) a)
    (hfa : FiltrationAtLeast background.syntheticTower N (a ≫ finiteExtensionMap background X Y f q)) :
    ∃ b : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN ((extensionSourceObject background X Y f).obj background.nu background.auxiliary) (q-i))),
      b ≫ ((background.quotients.tower _).triangle hi hiq).lambdaMap = a ∧
      FiltrationAtLeast background.syntheticTower (s+i) b ∧
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (finiteExtensionMap background X Y f (q-i))) ≫
          ((background.quotients.tower _).triangle hi hiq).lambdaMap =
        a ≫ finiteExtensionMap background X Y f q ∧
      FiltrationAtLeast background.syntheticTower N
        (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
          (finiteExtensionMap background X Y f (q-i))) :=
  KIP126.ProofTools.Internal.Leibniz.normalized_finite_division_of_kernel_no_crossing
    X Y f q i hi hiq s t N hsN hcross a ha hfa

end
end KIP126.ProofTools.Standard
