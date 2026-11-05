module

public import KIP126.ProofTools.GeneralizedLeibnizAtLevel
public import KIP126.ProofTools.GeneralizedMahowald.FiniteLevelAssembly
public import KIP126.AdamsComputation.Standard
import all KIP126.ProofTools.SyntheticProgramRules
import all KIP126.ProofTools.Paper.NumericalExamples
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.Paper.NuCofiberNumericalDifferential

/-! Fixed-model specializations of the extension-square, Leibniz and
Mahowald rules, and numerical conclusions with their specified actual labels.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Paper
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000


public def QuotientBoundaryCutoffStatement (A B : SyntheticObject (coefficients := background.coefficients))
    (g : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (q : ℕ) : Prop :=
  let QA : SyntheticObject (coefficients := background.coefficients) := .quotient q A
  let QB : SyntheticObject (coefficients := background.coefficients) := .quotient q B
  let SA : SyntheticObject (coefficients := background.coefficients) := .shift (1,-(q:ℤ)) A
  let SB : SyntheticObject (coefficients := background.coefficients) := .shift (1,-(q:ℤ)) B
  let top := background.convergentMap QA QB (XModLambdaN.map g q)
  let left := background.convergentMap QA SA ((XModLambdaN.proj (A.obj background.nu background.auxiliary) q ≫
    (KIP126.ProofTools.Internal.Mahowald.biSuspensionIso q (A.obj background.nu background.auxiliary)).inv))
  let bottom := background.convergentMap SA SB ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)
  let right := background.convergentMap QB SB ((XModLambdaN.proj (B.obj background.nu background.auxiliary) q ≫
    (KIP126.ProofTools.Internal.Mahowald.biSuspensionIso q (B.obj background.nu background.auxiliary)).inv))
  ∀ (p : ℤ × ℤ) (s M b L κ : ℤ)
    (_hM : 0 ≤ M) (_hb : 0 ≤ b) (_hL : 0 ≤ L)
    (_hκ : 0 < κ) (_hκD : κ ≤ b+L-M)
    (ξ : ((background.family.obj (QA.obj background.nu background.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (η : ((background.family.obj (QB.obj background.nu background.auxiliary)).sequence.ssData
      (s+M,p.1+(s+M),p.2)).eInfty)
    (ζ : ((background.family.obj (SA.obj background.nu background.auxiliary)).sequence.ssData
      (s+b,p.1+(s+b),p.2)).eInfty)
    (ω : ((background.family.obj (SB.obj background.nu background.auxiliary)).sequence.ssData
      (s+b+L,p.1+(s+b+L),p.2)).eInfty),
  TowerExtensionEquation top p s M ξ η →
  TowerExtensionEquation left p s b ξ ζ →
  TowerExtensionEquation bottom p (s+b) L ζ ω →
  ((∀ u v : ℤ, s < u → u ≤ v → v ≤ s+M →
      ∀ source target, ¬ TowerEssentialExtension top p u (v-u) source target) ∨
    (∀ u v : ℤ, s < u → u ≤ v → v ≤ s+b →
      ∀ source target, ¬ TowerEssentialExtension left p u (v-u) source target)) →
  (∀ u v : ℤ, s+b < u → u ≤ v → s+M+κ ≤ v → v ≤ s+b+L →
    ∀ source target, ¬ TowerEssentialExtension bottom p u (v-u) source target) →
  TowerExtensionEquation right p (s+M) (κ-1) η 0 →
  (∀ u v : ℤ, s+M < u → u ≤ v → v ≤ s+M+(κ-1) →
    ∀ source target, ¬ TowerEssentialExtension right p u (v-u) source target) →
  TowerExtensionEquation right p (s+M) (b+L-M) η
    ((eqToHom (congrArg (fun q => ((background.family.obj
      (SB.obj background.nu background.auxiliary)).sequence.ssData q).eInfty)
      (show (s+b+L,p.1+(s+b+L),p.2) =
        (s+M+(b+L-M),p.1+(s+M+(b+L-M)),p.2) by ext <;> dsimp <;> omega))) ω)

public theorem cutoffLeibnizSquare
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) : QuotientBoundaryCutoffStatement
      (extensionSourceObject background X Y f) (.nu Y)
      (background.normalizedMap X Y f).map q := by
  change KIP126.ProofTools.Internal.ProgramRules.QuotientBoundaryCutoffStatement
    (extensionSourceObject background X Y f) (.nu Y)
    (background.normalizedMap X Y f).map q
  exact KIP126.ProofTools.Internal.ProgramRules.cutoffLeibnizSquare X Y f q


public theorem ssCutoffSquareAtLevel
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page level : ℕ) (_hpage : 2 ≤ page) : QuotientBoundaryCutoffStatement
      (extensionSourceObject background X Y f) (.nu Y)
      (background.normalizedMap X Y f).map (page+level-1) := by
  change KIP126.ProofTools.Internal.ProgramRules.QuotientBoundaryCutoffStatement
    (extensionSourceObject background X Y f) (.nu Y)
    (background.normalizedMap X Y f).map (page+level-1)
  exact KIP126.ProofTools.Internal.ProgramRules.ssCutoffSquareAtLevel X Y f page level _hpage


public theorem ssLeibnizAtLevelZero
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (b M L s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+M,t+M))
    (u : Ambient background X (s+b,t+b-1))
    (v : Ambient background Y (s+b+L,t+b-1+L))
    (hpage : 2 ≤ page) (hpageb : (page:ℤ) ≤ b)
    (hM : (normalizedExponent background.classicalTower f:ℤ) ≤ M)
    (hMUpper : M ≤ (page:ℤ)-2+normalizedExponent background.classicalTower f)
    (hL : (normalizedExponent background.classicalTower f:ℤ) ≤ L)
    (hu : IsPermanent background X (s+b,t+b-1) u)
    (hv : IsPermanent background Y (s+b+L,t+b-1+L) v)
    (hdx : DifferentialAt background X b (s,t) (s+b,t+b-1) x u)
    (hFinite : KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page 0 M s t x y)
    (hInfinity : InfiniteExtension background X Y f L (s+b) (t+b-1) u v)
    (hsource : KIP126.ProofTools.Standard.LevelBoundaryNoCrossing X Y f page 0 b s t ∨
      KIP126.ProofTools.Standard.LevelFiniteNoCrossing X Y f page 0 M s t)
    (hbottom : KIP126.ProofTools.Standard.LevelBottomNoCrossing X Y f page 0 b L s t) :
    DifferentialAt background Y (b+L-M) (s+M,t+M) (s+b+L,t+b-1+L) y v := by
  exact KIP126.ProofTools.Internal.ProgramRules.ssLeibnizAtLevelZero
    X Y f page b M L s t x y u v hpage hpageb hM hMUpper hL hu hv
    hdx hFinite hInfinity hsource hbottom


public def FiniteMahowaldZeroInputStatement
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
    (n₁ m₁ k : ℕ) (_hn₁ : 0 < n₁) (s t : ℤ),
  let i : ℕ := 0
  let j : ℕ := 0
  let hj : j < n₁ := _hn₁
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

public theorem ssMahowaldZeroInputLevels (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1) :
    FiniteMahowaldZeroInputStatement T he := by
  change KIP126.ProofTools.Internal.ProgramRules.FiniteMahowaldZeroInputStatement T he
  exact KIP126.ProofTools.Internal.ProgramRules.ssMahowaldZeroInputLevels T he


end
end KIP126.ProofTools.Standard
end



@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background)
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


@[no_expose] public def p : background.classical.sphere.Page 2 (4,37) :=
  KIP126.ProofTools.Paper.NumericalExamples.p


public def h0p : background.classical.sphere.Page 2 (5,38) := product h0 p


public theorem paper6_7_classical_d3 :
    HasNonzeroDifferential background.classical.sphere 3 (2,36) (5,38)
      (KIP126.Literature.Standard.hiProduct 2 5) h0p := by
  change HasNonzeroDifferential background.classical.sphere 3 (2,36) (5,38)
    (KIP126.Literature.Standard.hiProduct 2 5)
    KIP126.ProofTools.Paper.NumericalExamples.h0p
  exact KIP126.ProofTools.Paper.NumericalExamples.paper6_7_classical_d3


end
end KIP126.ProofTools.Standard
end

/-! The specified suspended sphere label and its finite and full nu extensions. -/
@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background Spectrum)
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual classical suspension of the specified sphere class h0 h4^2
on S3. Every suspension relation and the final actual shift map is retained. -/
public def IsSphereThreeH0H4Square
    (x : Ambient background (.shift 3 .sphere) (3,36)) : Prop :=
  let e :
      ((AdamsObject.shift 1 (.shift 1 (.shift 1 .sphere))).obj background.auxiliary) ≅
        ((AdamsObject.shift 3 .sphere).obj background.auxiliary) :=
    (shiftFunctor Spectrum (1:ℤ)).mapIso
      (((shiftFunctorAdd' Spectrum (1:ℤ) 1 2 (by decide)).app
        (SphereSpectrum (C := Spectrum))).symm) ≪≫
      ((shiftFunctorAdd' Spectrum (2:ℤ) 1 3 (by decide)).app
        (SphereSpectrum (C := Spectrum))).symm
  ∃ (x1 : Ambient background (.shift 1 .sphere) (3,34))
    (x2 : Ambient background (.shift 1 (.shift 1 .sphere)) (3,35))
    (x3 : Ambient background (.shift 1 (.shift 1 (.shift 1 .sphere))) (3,36)),
    (background.classicalSuspension .sphere).DesuspendsClass 3 34 x1
      (product h0 (background.standardClasses.standardHiSquare 4)) ∧
    (background.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 3 35 x2 x1 ∧
    (background.classicalSuspension (.shift 1 (.shift 1 .sphere))).DesuspendsClass
      3 36 x3 x2 ∧
    (background.classical.map e.hom).pageMap 2 (3,36) x3 = x

/-- The finite E3 nu-extension with the fixed S3 source
and archived target, allowing zero page representatives. -/
public theorem paper6_19_finite_nu_extension :
    ∃ x : Ambient background (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      ReachesPage (background.classical.obj ((AdamsObject.shift 3 .sphere).obj
        background.auxiliary)) 3 (3,36) x ∧
      FiniteExtension background (.shift 3 .sphere) .sphere background.auxiliary.nuMap
        3 2 3 36 x h0p := by
  change KIP126.ProofTools.Paper.NumericalExamples.Paper6_19FiniteNuExtensionStatement
  exact KIP126.ProofTools.Paper.NuNumericalExtensions.paper6_19_finite_nu_extension

/-- The full nu-extension with its prescribed source and image. -/
public theorem paper6_24_infinite_nu_extension :
    ∃ x : Ambient background (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      InfiniteExtension background (.shift 3 .sphere) .sphere background.auxiliary.nuMap
        2 3 36 x h0p := by
  change KIP126.ProofTools.Paper.NumericalExamples.Paper6_24InfiniteNuExtensionStatement
  exact KIP126.ProofTools.Paper.NuNumericalExtensions.paper6_24_infinite_nu_extension

end
end KIP126.ProofTools.Standard
end


/-! The actual nu-cofiber differential, retaining both cell-map labels. -/
@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background)
open KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Existence of a cofiber source above the suspension of h0 h4^2 on S3,
with the specified top and bottom E2 maps, d2 value, and permanent bottom value.
The differential relation allows zero page representatives. -/
public theorem paper6_19_actual_cofiber_d2 :
    ∃ x : Ambient background (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      x ∈ permanentCycles background (.shift 3 .sphere) (3,36) ∧
      ∃ uTop : Ambient background (.shift 1 (.shift 3 .sphere)) (3,37),
        (background.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 3 37 uTop x ∧
        ∃ xbar : Ambient background .nuCofiber (3,37),
          (background.classical.map background.auxiliary.nuRouteTriangle.h).pageMap 2 (3,37) xbar = uTop ∧
          DifferentialAt background .nuCofiber 2 (3,37) (5,38) xbar
            ((background.classical.map background.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38) h0p) ∧
          IsPermanent background .nuCofiber (5,38)
            ((background.classical.map background.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38) h0p) := by
  exact KIP126.ProofTools.Paper.NuCofiberNumericalDifferential.paper6_19_actual_cofiber_d2

end
end KIP126.ProofTools.Standard
end
