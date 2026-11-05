module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyDifferential

/-! The ordinary-first early-d₂ consequences. These are exact specializations
of the higher early-boundary theorems at i = 1. The empty intermediate root
range is discharged internally; the actual terminal and image conditions
remain part of each statement. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

/-- The ordinary second branch with an early d₂ at the target end. -/
public theorem ordinary_d2_early_target_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (N d : ℕ)
    (hiN : 1 < N)
    (hd : 0 < d)
    (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (y : Ambient background T.Y (s,t))
    (hy : y-(background.classical.map T.f).pageMap 2 (s,t) x∈boundaries background T.Y N (s,t))
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y ((s+N)+d+1,(t+N)+d))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 → permanentCycles background T.Y (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z (((s+N)+1)+j-1+1,(t+N)+j+1),
          z ∈ cycles background T.Z (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j+1) ∧
        ∃ u : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
          (background.classicalSuspension T.X).DesuspendsClass (((s+N)+1)+j-1+1) ((t+N)+j+1)
            ((background.classical.map T.h).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j))
    (c : Ambient background T.Y ((s+N)-1,(t+N)-1))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (1+1) (((s+N)-1),((t+N)-1)) ((s+N)+1,(t+N)) c ((background.classical.map T.f).pageMap 2 ((s+N)+1,(t+N)) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((1+d)+1) (((s+N)-1)+1,((t+N)-1)+1) (((s+N)+d+1)+1,((t+N)+d)+1)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) ((s+N)-1) ((t+N)-1) c)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) ((s+N)+d+1) ((t+N)+d) v))
    (hH : ∀ z : Ambient background T.Z (((s+N)-1)+(1+1),(((t+N)-1)+(1+1)-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (((s+N)-1)+(1+1)) (((t+N)-1)+(1+1)-1) z ∈
        boundaries background T.X (1+1) (((s+N)-1)+(1+1),((t+N)-1)+(1+1)-1))
    (P : Submodule ℤ (Ambient background T.Y ((s+N)+d+1,(t+N)+d)))
    (hP : permanentCycles background T.Y ((s+N)+d+1,(t+N)+d)≤P)
    (hv : v∈P)
    (hker : ∀ z∈P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) ((s+N)+d+1) ((t+N)+d) z=0 →
      z∈boundaries background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d)) :
    IsCycle background T.Y (N+d:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d) v ∧
      DifferentialAt background T.Y ((N+d:ℕ)+1) (s,t) ((s+N)+d+1,(t+N)+d) y v := by
  exact ordinary_early_target_second
    T he hf hg hh N 1 d (by decide) hiN hd s t x y hy u hdx v Pm hPm hmid c hearly hdroot (by intro p hp hp'; omega) hH P hP hv hker

/-- The ordinary third branch with an early d₂ at the target end. -/
public theorem ordinary_d2_early_target_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (N d : ℕ)
    (hiN : 1 < N)
    (hd : 0 < d)
    (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (y : Ambient background T.Y (s,t))
    (hy : y-(background.classical.map T.f).pageMap 2 (s,t) x∈boundaries background T.Y N (s,t))
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y ((s+N)+d+1,(t+N)+d))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 → permanentCycles background T.Y (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z (((s+N)+1)+j-1,(t+N)+j),
          z ∈ cycles background T.Z (((d+1):ℤ)-j) (((s+N)+1)+j-1,(t+N)+j) ∧
        ∃ u : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
          (background.classicalSuspension T.X).DesuspendsClass (((s+N)+1)+j-1+1) ((t+N)+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (((s+N)+1)+j-1) ((t+N)+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j))
    (c : Ambient background T.Y ((s+N)-1,(t+N)-1))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (1+1) (((s+N)-1),((t+N)-1)) ((s+N)+1,(t+N)) c ((background.classical.map T.f).pageMap 2 ((s+N)+1,(t+N)) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((1+d)+1) (((s+N)-1),((t+N)-1)) (((s+N)+d+1),((t+N)+d)) ((background.classical.map T.g).pageMap 2 (((s+N)-1),((t+N)-1)) c)
      ((background.classical.map T.g).pageMap 2 (((s+N)+d+1),((t+N)+d)) v))
    (hH : ∀ z : Ambient background T.Z (((s+N)-1)+(1+1)-1,((t+N)-1)+(1+1)-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (((s+N)-1)+(1+1)-1) (((t+N)-1)+(1+1)-1) z ∈
          boundaries background (.shift 1 T.X) (1+1) ((((s+N)-1)+(1+1)-1)+1,(((t+N)-1)+(1+1)-1)+1))
    (P : Submodule ℤ (Ambient background T.Y ((s+N)+d+1,(t+N)+d)))
    (hP : permanentCycles background T.Y ((s+N)+d+1,(t+N)+d)≤P)
    (hv : v∈P)
    (hker : ∀ z∈P, (background.classical.map T.g).pageMap 2 ((s+N)+d+1,(t+N)+d) z=0 →
      z∈boundaries background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d)) :
    IsCycle background T.Y (N+d:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d) v ∧
      DifferentialAt background T.Y ((N+d:ℕ)+1) (s,t) ((s+N)+d+1,(t+N)+d) y v := by
  exact ordinary_early_target_third
    T he hf hg hh N 1 d (by decide) hiN hd s t x y hy u hdx v Pm hPm hmid c hearly hdroot (by intro p hp hp'; omega) hH P hP hv hker

/-- The ordinary second branch with an early d₂ at the source end. -/
public theorem ordinary_d2_early_source_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (d N : ℕ)
    (hd : 0 < d)
    (hKN : d+1≤N)
    (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (y : Ambient background T.Y (B+d+1,W+d))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (c : Ambient background T.Y (B-1,W-1))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (1+1) ((B-1),(W-1)) (B+1,W) c ((background.classical.map T.f).pageMap 2 (B+1,W) x))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((1+d)+1) ((B-1)+1,(W-1)+1) ((B+d+1)+1,(W+d)+1)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (B-1) (W-1) c)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (B+d+1) (W+d) y))
    (hH : ∀ z : Ambient background T.Z ((B-1)+(1+1),((W-1)+(1+1)-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((B-1)+(1+1)) ((W-1)+(1+1)-1) z ∈
        boundaries background T.X (1+1) ((B-1)+(1+1),(W-1)+(1+1)-1))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (d+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (himage : ∀ e : Ambient background T.X (B+d+1,W+d),
      (background.classical.map T.f).pageMap 2 (B+d+1,W+d) e∈cycles background T.Y ((N-d:ℕ)+1) (B+d+1,W+d)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-d:ℕ) (B+d+1,W+d) y ∧
      IsCycle background T.Y (N-d:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-d:ℕ)+1) (B+d+1,W+d) ((B+1)+N+1,W+N) y v := by
  exact ordinary_early_source_second
    T he hf hg hh 1 d N (by decide) hd hKN B W x u y hdx c hearly hdroot (by intro p hp hp'; omega) hH hmid himage

/-- The ordinary third branch with an early d₂ at the source end. -/
public theorem ordinary_d2_early_source_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (d N : ℕ)
    (hd : 0 < d)
    (hKN : d+1≤N)
    (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (y : Ambient background T.Y (B+d+1,W+d))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (c : Ambient background T.Y (B-1,W-1))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (1+1) ((B-1),(W-1)) (B+1,W) c ((background.classical.map T.f).pageMap 2 (B+1,W) x))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((1+d)+1) ((B-1),(W-1)) ((B+d+1),(W+d)) ((background.classical.map T.g).pageMap 2 ((B-1),(W-1)) c)
      ((background.classical.map T.g).pageMap 2 ((B+d+1),(W+d)) y))
    (hH : ∀ z : Ambient background T.Z ((B-1)+(1+1)-1,(W-1)+(1+1)-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        ((B-1)+(1+1)-1) ((W-1)+(1+1)-1) z ∈
          boundaries background (.shift 1 T.X) (1+1) (((B-1)+(1+1)-1)+1,((W-1)+(1+1)-1)+1))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (d+1)-1 →
      ∀ a : Ambient background T.X ((B+1)+j-1+1,W+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((B+1)+j-1+1,W+j) →
        ∃ z' : Ambient background T.Z ((B+1)+j-1,W+j),
          z' ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u' : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z') (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1) ((B+1)+j-1+1,W+j))
    (himage : ∀ e : Ambient background T.X (B+d+1,W+d),
      (background.classical.map T.f).pageMap 2 (B+d+1,W+d) e∈cycles background T.Y ((N-d:ℕ)+1) (B+d+1,W+d)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-d:ℕ) (B+d+1,W+d) y ∧
      IsCycle background T.Y (N-d:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-d:ℕ)+1) (B+d+1,W+d) ((B+1)+N+1,W+N) y v := by
  exact ordinary_early_source_third
    T he hf hg hh 1 d N (by decide) hd hKN B W x u y hdx c hearly hdroot (by intro p hp hp'; omega) hH hmid himage

end
end KIP126.ProofTools.Internal.SyntheticCoverage
