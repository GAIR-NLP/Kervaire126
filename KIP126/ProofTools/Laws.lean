module



public import KIP126.ProofTools.Language

/-! Actual page labels and crossing predicates for the paper's reusable tools. -/

@[expose] section
namespace KIP126.ProofTools
noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : AdamsSyntheticBackground C Syn)

/-- AimPaper Theorem 6.1 (`thm:e73f481e`) on one spectral sequence `D`.
The final bidegree is `(s+r+l,t+r+l-1)`. The proposition includes zero
differentials and extensions; its proof uses the literature comparisons
and the paper’s δ/λ/ρ argument. -/
public def GeneralizedLeibnizLaw (X Y : AdamsObject (coefficients := D.coefficients)) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) : Prop :=
  ∀ (page : ℕ) (r m l s t : ℤ)
    (x : Ambient D X (s, t)) (y : Ambient D Y (s + m, t + m))
    (xInfinity : Ambient D X (s + r, t + r - 1))
    (yInfinity : Ambient D Y (s + r + l, t + r - 1 + l)),
    2 ≤ page → (page : ℤ) ≤ r →
    (normalizedExponent D.classicalTower f : ℤ) ≤ m →
    m ≤ (page : ℤ) - 2 + normalizedExponent D.classicalTower f →
    (normalizedExponent D.classicalTower f : ℤ) ≤ l →
    IsCycle D X (r - 1) (s, t) x →
    IsCycle D Y (r - 1 - m + normalizedExponent D.classicalTower f) (s + m, t + m) y →
    IsPermanent D X (s + r, t + r - 1) xInfinity →
    IsPermanent D Y (s + r + l, t + r - 1 + l) yInfinity →
    DifferentialAt D X r (s, t) (s + r, t + r - 1) x xInfinity →
    FiniteExtension D X Y f page m s t x y →
    InfiniteExtension D X Y f l (s + r) (t + r - 1) xInfinity yInfinity →
    (NoCrossingOn D X r page (s, t) ∨
      FiniteNoCrossing D X Y f page m s t) →
    InfiniteNoCrossing D X Y f l (s + r) (t + r - 1) →
    DifferentialAt D Y (r + l - m) (s + m, t + m)
      (s + r + l, t + r - 1 + l) y yInfinity


/-- The actual-triangle formulation of AimPaper Theorem 6.12 (`thm:158d451a`).
The second no-crossing branch concerns `d_r` on `Z`, checked on `E_r′`.
The target of `h` lies in `ΣX`; `D.classicalSuspension` and raw-cycle
representatives relate its label to `x`. The conclusion gives an
f-extension target congruent to `y` modulo `B_r′`. The exponent sum and
length bounds ensure positivity of `r′` and of the conclusion’s page. -/
public def GeneralizedMahowaldLaw (T : TriangleData D.auxiliary) : Prop :=
  ∀ he : (normalizedExponent D.classicalTower T.f : ℤ) + normalizedExponent D.classicalTower T.g +
      normalizedExponent D.classicalTower T.h = 1,
  KIP126.Literature.NormalizedTriangleCompatible D T he →
  ∀ (n m l s t : ℤ),
    let r := n + m + l
    let n₁ := n - normalizedExponent D.classicalTower T.f
    let m₁ := m - normalizedExponent D.classicalTower T.g
    let l₁ := l - normalizedExponent D.classicalTower T.h
    let r' := r - m₁
    ∀ (x : Ambient D (T.X) (s + l, t + l - 1))
      (y : Ambient D (T.Y) (s + l + n, t + l - 1 + n))
      (xBar : Ambient D (T.Z) (s, t))
      (yBar : Ambient D (T.Z) (s + l + n + m, t + l - 1 + n + m))
      (suspendedX : Ambient D (.shift 1 T.X) (s + l, t + l)),
      1 ≤ n₁ → 0 ≤ m₁ → 0 ≤ l₁ →
      IsCycle D (T.X) n₁ (s + l, t + l - 1) x →
      IsCycle D (T.Y) (m₁ + 1) (s + l + n, t + l - 1 + n) y →
      IsCycle D (T.Z) (r - 1) (s, t) xBar →
      IsPermanent D (T.Z) (s + l + n + m, t + l - 1 + n + m) yBar →
      (D.classicalSuspension T.X).DesuspendsClass (s + l) (t + l) suspendedX x →
      FiniteExtension D T.Z (.shift 1 T.X) T.h r'.toNat l s t xBar suspendedX →
      DifferentialAt D (T.Z) r (s, t)
        (s + l + n + m, t + l - 1 + n + m) xBar yBar →
      (FiniteNoCrossing D T.Z (.shift 1 T.X) T.h r'.toNat l s t ∨
        NoCrossingOn D (T.Z) r r' (s, t)) →
      FiniteExtension D T.Y T.Z T.g (m₁ + 2).toNat m (s + l + n) (t + l - 1 + n) y yBar →
      IsCycle D (T.X) (n + m + normalizedExponent D.classicalTower T.h) (s + l, t + l - 1) x ∧
        ∃ y' : Ambient D (T.Y) (s + l + n, t + l - 1 + n),
          FiniteExtension D T.X T.Y T.f (n + m + 1 + normalizedExponent D.classicalTower T.h).toNat
            n (s + l) (t + l - 1) x y' ∧
          Congruent D (T.Y) r' (s + l + n, t + l - 1 + n) y' y


/-- A sufficient condition for finite-page stretching.
Source and target satisfy the specified later-page cycle conditions.
The excluded obstructions are shorter extensions in the same earlier
quotient, with source outside the later `ρ`-induced `E∞` image and nonzero
target, including inessential extensions. Under these hypotheses, an
earlier-page extension supplies a later-page extension with the same labels. -/
public def FinitePageExtensionStretchingLaw (X Y : AdamsObject (coefficients := D.coefficients)) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) : Prop :=
  ∀ (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient D X (s, t)) (y : Ambient D Y (s + n, t + n)),
    2 ≤ rEarlier → rEarlier ≤ rLater →
    (normalizedExponent D.classicalTower f : ℤ) ≤ n →
    n ≤ (rEarlier : ℤ) - 2 + normalizedExponent D.classicalTower f →
    IsCycle D X ((rLater : ℤ) - 1) (s, t) x →
    IsCycle D Y ((rLater : ℤ) - 1 - n + normalizedExponent D.classicalTower f) (s + n, t + n) y →
    FiniteExtension D X Y f rEarlier n s t x y →
    ¬ FiniteExtensionNonliftableCrossing D X Y f rEarlier rLater n s t →
    FiniteExtension D X Y f rLater n s t x y


end
end KIP126.ProofTools
