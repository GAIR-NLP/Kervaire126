module

public import KIP126.ProofTools.GeneralizedMahowald.ActualNoCrossing
public import KIP126.ProofTools.Language
public import KIP126.ProofTools.ConvergenceOperations
public import KIP126.ProofTools.LevelLanguage

/-! Finite-level Mahowald target with a common lift for both image
equations and a no-crossing premise on essential extensions. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Double-input-layer finite Mahowald assertion in the normalized triangle,
including arithmetic conditions, classical labels, extension relations,
representatives, and detections. Shifted finite labels use
`levelFiniteSourceLabel`. Natural parameters encode `n₁≥1`, `m₁≥0`,
`k≥0`, `i≥0`, and `0≤j<n₁`; adding the normalization exponents recovers
`n,m,l`. Both signed image equations retain ordinary suspension.
Quotient-shift comparisons preserve the inclusion and the rho square
on sphere representatives. -/
public def FiniteMahowaldAtLevelStatement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1) : Prop :=
  let shiftFinitePageLabel (V : SyntheticObject (coefficients := background.coefficients)) (δ : ℤ × ℤ)
      (q : Tridegree)
      (x : (background.family.obj (V.obj background.nu background.auxiliary)).E₂ q) :
      (background.family.obj ((SyntheticObject.shift δ V).obj background.nu background.auxiliary)).E₂
        (q.1,q.2.1+δ.1,q.2.2+δ.2) :=
    regradeE2 (by
      ext <;> dsimp
      omega)
      ((KIP126.AdamsSynthetic.Completed.shift_page δ V 2 (by decide)
        (q.2.1-q.1,q.2.2) q.1).hom (regradeE2 (by ext <;> simp) x))
  ∀
    (n₁ m₁ k i j : ℕ) (_hn₁ : 0 < n₁) (hj : j < n₁) (s t : ℤ),
  let ef : ℤ := normalizedExponent background.classicalTower T.f
  let eg : ℤ := normalizedExponent background.classicalTower T.g
  let eh : ℤ := normalizedExponent background.classicalTower T.h
  let n : ℤ := n₁+ef
  let m : ℤ := m₁+eg
  let l : ℤ := k+eh
  let r : ℤ := n+m+l
  let A : ℕ := n₁+k+i-j
  let B : ℕ := m₁+j+1
  let N : ℕ := A+B
  let K : ℕ := i+k
  let J : ℕ := A+j
  let Q : ℕ := N-K
  let V := normalizedTriangle background T he
  let VX : SyntheticObject (coefficients := background.coefficients) := .shift (0,ef) (.nu T.X)
  let VY : SyntheticObject (coefficients := background.coefficients) := .nu T.Y
  let VZ : SyntheticObject (coefficients := background.coefficients) := .shift (0,-eg) (.nu T.Z)
  let QA : SyntheticObject (coefficients := background.coefficients) := .quotient A VZ
  let HA : SyntheticObject (coefficients := background.coefficients) := .shift (1,0) (.quotient A VX)
  let DB : SyntheticObject (coefficients := background.coefficients) := .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B VZ))
  let GB : SyntheticObject (coefficients := background.coefficients) := .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B VY))
  let CN : SyntheticObject (coefficients := background.coefficients) := .shift (1,0) (.quotient N VX)
  let FN : SyntheticObject (coefficients := background.coefficients) := .shift (1,0) (.quotient N VY)
  let p : ℤ × ℤ := (t-s,t-i-eg)
  let hA : 0 < A := by dsimp [A]; omega
  let hAN : A < N := by dsimp [N,B]; omega
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
  let LZ := (background.quotients.tower V.obj₃).triangle hA hAN
  let LY := (background.quotients.tower V.obj₂).triangle hA hAN
  let delta : XModLambdaN V.obj₃ A ⟶ (F.obj (XModLambdaN V.obj₃ B))⟦(1:ℤ)⟧ := by
    simpa only [N,Nat.add_sub_cancel_left] using LZ.delta
  let lambdaY : F.obj (XModLambdaN V.obj₂ B) ⟶ XModLambdaN V.obj₂ N := by
    simpa only [N,Nat.add_sub_cancel_left] using LY.lambdaMap
  ∀ (exA : XModLambdaN (V.obj₁⟦(1:ℤ)⟧) A ≅
      (XModLambdaN V.obj₁ A)⟦(1:ℤ)⟧)
    (exN : XModLambdaN (V.obj₁⟦(1:ℤ)⟧) N ≅
      (XModLambdaN V.obj₁ N)⟦(1:ℤ)⟧)
    (eyN : XModLambdaN (V.obj₂⟦(1:ℤ)⟧) N ≅
      (XModLambdaN V.obj₂ N)⟦(1:ℤ)⟧),
  XModLambdaN.incl _ A ≫ exA.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₁ A) →
  XModLambdaN.incl _ N ≫ exN.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₁ N) →
  XModLambdaN.incl _ N ≫ eyN.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₂ N) →
  let hmap : QA.obj background.nu background.auxiliary ⟶ HA.obj background.nu background.auxiliary :=
    XModLambdaN.map V.mor₃ A ≫ exA.hom ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let dmap : QA.obj background.nu background.auxiliary ⟶ DB.obj background.nu background.auxiliary :=
    delta ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let gmap : GB.obj background.nu background.auxiliary ⟶ DB.obj background.nu background.auxiliary :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _ ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map V.mor₂ B)) ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let Mh := background.convergentMap QA HA hmap
  let Md := background.convergentMap QA DB dmap
  let Mg := background.convergentMap GB DB gmap
  ∀ (xbar : Ambient background T.Z (s,t))
    (x : Ambient background T.X (s+l,t+l-1))
    (y : Ambient background T.Y (s+l+n,t+l+n-1))
    (ybar : Ambient background T.Z (s+r,t+r-1)),
  IsCycle background T.Z (r-1) (s,t) xbar →
  DifferentialAt background T.Z r (s,t) (s+r,t+r-1) xbar ybar →
  IsPermanent background T.Z (s+r,t+r-1) ybar →
  IsCycle background T.X (n₁-j) (s+l,t+l-1) x →
  IsCycle background T.Y (m₁+1) (s+l+n,t+l+n-1) y →
  let xbarA : (background.family.obj (QA.obj background.nu background.auxiliary)).E₂
      (s,p.1+s,p.2) :=
    regradeE2 (by
      ext <;> dsimp [p]
      omega)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.Z A (-eg) s t i xbar)
  let xA : (background.family.obj (HA.obj background.nu background.auxiliary)).E₂
      (s+l,p.1+(s+l),p.2) :=
    regradeE2 (by
      ext <;> dsimp [p,l,K,ef,eg,eh] at * <;> omega)
      (shiftFinitePageLabel (.quotient A VX) (1,0) _
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.X A ef (s+l) (t+l-1) K x))
  let yB : (background.family.obj (GB.obj background.nu background.auxiliary)).E₂
      (s+l+n,p.1+(s+l+n),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,l,n,A,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.shift (0,-(A:ℤ)) (.quotient B VY)) (1,0) _
        (shiftFinitePageLabel (.quotient B VY) (0,-(A:ℤ)) _
          (finiteTargetLabel background T.Y B (s+l+n) (t+l+n-1) j y)))
  let ybarB : (background.family.obj (DB.obj background.nu background.auxiliary)).E₂
      (s+r,p.1+(s+r),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,r,l,n,m,A,B,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.shift (0,-(A:ℤ)) (.quotient B VZ)) (1,0) _
        (shiftFinitePageLabel (.quotient B VZ) (0,-(A:ℤ)) _
          (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.Z B (-eg) (s+r) (t+r-1) (B-1) ybar)))
  let xN : (background.family.obj (CN.obj background.nu background.auxiliary)).E₂
      (s+l,p.1+(s+l),p.2) :=
    regradeE2 (by
      ext <;> dsimp [p,l,K,ef,eg,eh] at * <;> omega)
      (shiftFinitePageLabel (.quotient N VX) (1,0) _
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.X N ef (s+l) (t+l-1) K x))
  let yN : (background.family.obj (FN.obj background.nu background.auxiliary)).E₂
      (s+l+n,p.1+(s+l+n),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,l,n,A,J,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.quotient N VY) (1,0) _
        (finiteTargetLabel background T.Y N (s+l+n) (t+l+n-1) J y))
  ∀ (e0 : ((background.family.obj (QA.obj background.nu background.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty)
    (ex : ((background.family.obj (HA.obj background.nu background.auxiliary)).sequence.ssData
        (s+l,p.1+(s+l),p.2)).eInfty)
    (ey : ((background.family.obj (GB.obj background.nu background.auxiliary)).sequence.ssData
        (s+l+n,p.1+(s+l+n),p.2)).eInfty)
    (ez : ((background.family.obj (DB.obj background.nu background.auxiliary)).sequence.ssData
        (s+r,p.1+(s+r),p.2)).eInfty),
  HasInfinityRepresentative _ 2 _ xbarA e0 →
  HasInfinityRepresentative _ 2 _ xA ex →
  HasInfinityRepresentative _ 2 _ yB ey →
  HasInfinityRepresentative _ 2 _ ybarB ez →
  TowerExtensionEquation Mh p s l e0 ex →
  TowerExtensionEquation Md p s r e0 ez →
  TowerExtensionEquation Mg p (s+l+n) m ey
    ((eqToHom (congrArg (fun q =>
      ((background.family.obj (DB.obj background.nu background.auxiliary)).sequence.ssData q).eInfty)
      (show (s+r,p.1+(s+r),p.2)=(s+l+n+m,p.1+(s+l+n+m),p.2) by
        ext <;> dsimp [r] <;> omega))) ez) →
  (ActualNoCrossing Mh p s l ∨ ActualNoCrossing Md p s r) →
  ∃ (a : BiHom p.1 p.2 (XModLambdaN V.obj₃ A))
    (b : BiHom p.1 p.2 ((F.obj (XModLambdaN V.obj₂ B))⟦(1:ℤ)⟧))
    (c : BiHom p.1 p.2 (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) N)),
    Detects (background.convergence QA) (s,p.1+s,p.2) xbarA
      (homotopyRegrade (by dsimp [p]; omega) rfl a) ∧
    Detects (background.convergence HA) (s+l,p.1+(s+l),p.2) xA
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ hmap)) ∧
    Detects (background.convergence DB) (s+r,p.1+(s+r),p.2) ybarB
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ dmap)) ∧
    Detects (background.convergence GB) (s+l+n,p.1+(s+l+n),p.2) yB
      (homotopyRegrade (by dsimp; omega) rfl
        (b ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    Detects (background.convergence DB) (s+r,p.1+(s+r),p.2) ybarB
      (homotopyRegrade (by dsimp; omega) rfl
        (b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (F.map (XModLambdaN.map V.mor₂ B)) ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    a ≫ delta = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (F.map (XModLambdaN.map V.mor₂ B)) ∧
    c ≫ (background.quotients.tower (V.obj₁⟦(1:ℤ)⟧)).rho A N hAN.le =
      a ≫ XModLambdaN.map V.mor₃ A ∧
    c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N ≫
      eyN.hom = -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaY) ∧
    Detects (background.convergence CN) (s+l,p.1+(s+l),p.2) xN
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ exN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    Detects (background.convergence FN) (s+l+n,p.1+(s+l+n),p.2) yN
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N ≫
          eyN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    IsCycle background T.X Q (s+l,t+l-1) x ∧
    KIP126.ProofTools.Standard.LevelFiniteExtension T.X T.Y T.f
      (Q+1) K n (s+l) (t+l-1) x
      ((eqToHom (congrArg (fun q => (background.classical.obj
          (T.Y.obj background.auxiliary)).Page 2 q)
        (show (s+l+n,t+l+n-1)=(s+l+n,t+l-1+n) by ext <;> omega))) y)

end
end KIP126.ProofTools.Standard
