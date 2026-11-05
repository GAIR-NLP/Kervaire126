module

public import KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.LevelGL
import all KIP126.ProofTools.GeneralizedLeibniz.LevelZero

/-! The generalized Leibniz rule at an explicit lambda level.
The four-edge argument uses the extension and crossing conditions
at the specified quotient and weight. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed
noncomputable section

/-- AimPaper's generalized Leibniz square at any source lambda level.
The finite extension is in quotient `page + level - 1`. Its upper or left
edge must have no crossing, and its actual propagated bottom edge must have
no crossing. There is no upper bound on `level`. The infinite input is the
original zero-level extension; its propagation follows from the specified
quotient maps. -/
public theorem generalizedLeibnizAtLevel
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (r m l s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (xInfinity : Ambient background X (s+r,t+r-1))
    (yInfinity : Ambient background Y (s+r+l,t+r-1+l))
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r)
    (hm : (normalizedExponent background.classicalTower f:ℤ) ≤ m)
    (hmUpper : m ≤ (page:ℤ)-2+normalizedExponent background.classicalTower f)
    (hl : (normalizedExponent background.classicalTower f:ℤ) ≤ l)
    (hxInfinity : IsPermanent background X (s+r,t+r-1) xInfinity)
    (hyInfinity : IsPermanent background Y (s+r+l,t+r-1+l) yInfinity)
    (hdx : DifferentialAt background X r (s,t) (s+r,t+r-1) x xInfinity)
    (hFinite : LevelFiniteExtension X Y f page level m s t x y)
    (hInfinity : InfiniteExtension background X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hsourceCrossing : LevelBoundaryNoCrossing X Y f page level r s t ∨
      LevelFiniteNoCrossing X Y f page level m s t)
    (hbottomCrossing : LevelBottomNoCrossing X Y f page level r l s t) :
    DifferentialAt background Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y yInfinity := by
  obtain ⟨WFinite⟩ := (levelFiniteExtension_iff_internal X Y f page level m s t x y).mp hFinite
  obtain ⟨WInfinity⟩ := hInfinity
  exact KIP126.ProofTools.Internal.Leibniz.generalizedLeibniz_at_level
    X Y f page level r m l s t x y xInfinity yInfinity hpage hpr hm hmUpper hl
    hxInfinity hyInfinity hdx WFinite WInfinity
    (hsourceCrossing.imp
      (levelBoundaryNoCrossing_iff_internal X Y f page level r s t).mp
      (levelFiniteNoCrossing_iff_internal X Y f page level m s t).mp)
    ((levelBottomNoCrossing_iff_internal X Y f page level r l s t).mp hbottomCrossing)

/-- Convert an original finite extension to the corresponding zero-level
finite input, preserving its map equation and comparing its representative labels. -/
public theorem finiteExtensionAtLevelZero
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (h : FiniteExtension background X Y f page m s t x y) :
    LevelFiniteExtension X Y f page 0 m s t x y := by
  obtain ⟨W⟩ := h
  apply (levelFiniteExtension_iff_internal X Y f page 0 m s t x y).mpr
  exact ⟨KIP126.ProofTools.Internal.Leibniz.level_finite_extension_of_zero
    X Y f page m s t x y W⟩

end
end KIP126.ProofTools.Standard
