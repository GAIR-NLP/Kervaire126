module

public import KIP126.AdamsSynthetic

/-! Pstrągowski Lemma 4.23 and BHS Lemma 9.15 for one coefficient object,
ν functor and Adams tower. Application to selected normalized maps requires
comparison with the specified lifts and compatible ν-cofiber triangle. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : AdamsSyntheticBackground C Syn)

/-- A cofiber triangle with first two arrows νf and νg and a chosen
synthetic connecting map. -/
public def NuImageIsCofiber (T : Triangle C) : Prop :=
  ∃ δ : D.nu.functor.obj T.obj₃ ⟶ (D.nu.functor.obj T.obj₁)⟦(1 : ℤ)⟧,
    Triangle.mk (D.nu.functor.map T.mor₁) (D.nu.functor.map T.mor₂) δ ∈ distTriang Syn

/-- Pstrągowski's cofiber criterion for distinguished classical triangles. -/
public def NuCofiberCriterion : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    (NuImageIsCofiber D T ↔ HomologyShortExact D.coefficients T)

/-- An actual λᵏ factorization of νf in the negative-target convention. -/
public structure SyntheticFullLift {X Y : C} (f : X ⟶ Y) (k : ℕ) where
  map : D.nu.functor.obj X ⟶
    (SyntheticCategory.biShift (0,-(k : ℤ))).obj (D.nu.functor.obj Y)
  factorization : map ≫ lambdaPow k (D.nu.functor.obj Y) = D.nu.functor.map f

/-- BHS full lift for every pair of classical objects and every filtration
bound. The premise is factorization through D's actual target tower. -/
public def SyntheticLiftComparison : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (k : ℕ),
    MapFiltrationAtLeast D.classicalTower f k → Nonempty (SyntheticFullLift D f k)

/-- One triangle lift binds factorization and distinguishedness to the same
connecting arrow, using the given ν suspension comparison. -/
public structure SyntheticTriangleLift (T : Triangle C) where
  connecting : D.nu.functor.obj T.obj₃ ⟶
    (SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj (T.obj₁⟦(1 : ℤ)⟧))
  factorization : connecting ≫ SyntheticCategory.lam.app
    (D.nu.functor.obj (T.obj₁⟦(1 : ℤ)⟧)) = D.nu.functor.map T.mor₃
  distinguished : Triangle.mk (D.nu.functor.map T.mor₁) (D.nu.functor.map T.mor₂)
    (connecting ≫ (D.nu.boundaryLandingIso T.obj₁).hom) ∈ distTriang Syn

/-- λ torsion in a Hom group. -/
public def LambdaTorsion {X Y : Syn} (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, lambdaPow n X ≫ f = 0

/-- Reduce a full lift to one λ division. -/
public def SyntheticFullLift.normalizedMap {X Y : C} {f : X ⟶ Y} {k : ℕ}
    (L : SyntheticFullLift D f k) (hk : 1 ≤ k) :
    D.nu.functor.obj X ⟶ (SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj Y) := by
  have hdegree : ((0 : ℤ), -(k : ℤ)) =
      ((0 : ℤ), -1) + ((0 : ℤ), -((k-1 : ℕ) : ℤ)) := by
    ext <;> simp
    omega
  exact L.map ≫ eqToHom (congrArg
    (fun p : ℤ × ℤ => (SyntheticCategory.biShift p).obj (D.nu.functor.obj Y)) hdegree) ≫
    (SyntheticCategory.biShift_comp (0,-1) (0,-((k-1 : ℕ) : ℤ))).inv.app
      (D.nu.functor.obj Y) ≫
    lambdaPow (k-1) ((SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj Y))

/-- Full lifts agree with the selected triangle component modulo λ torsion. -/
public def SyntheticTriangleLift.FullLiftComparison {T : Triangle C}
    (L : SyntheticTriangleLift D T) : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (F : SyntheticFullLift D T.mor₃ k),
    LambdaTorsion (L.connecting - F.normalizedMap D hk)

/-- BHS triangle lifting, retaining positive filtration and all short-exact
conditions. All objects range over the full classical category. -/
public def SyntheticTriangleLiftComparison : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    MapFiltrationAtLeast D.classicalTower T.mor₃ 1 → HomologyShortExact D.coefficients T →
      ∃ L : SyntheticTriangleLift D T, L.FullLiftComparison D

/-- Three lifting statements on the same background. Application to a
selected normalized map requires comparison with the specified lifts. -/
private structure LiftSourceResults : Prop where
  nu_cofiber : NuCofiberCriterion D
  lift : SyntheticLiftComparison D
  triangle_lift : SyntheticTriangleLiftComparison D

end
end KIP126.Literature
