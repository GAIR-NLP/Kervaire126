module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.OrdinarySourceFinite

/-! Lower-length-one cases of the known-source criterion. For `K₂=1`
the lower intermediate-layer family is empty. The ordinary `K₁=1` case
is naturality; for `K₁≥2` the source-finite bottom-one theorem applies
under the complete upper hypotheses. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed KIP126.Core.SpectralSequence
open KIP126.Literature KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

/-- With K₁=K₂=1 the page remains r and both named images are transported
by the actual ordinary spectral-sequence morphism. -/
public theorem known_source_differential_ordinary_top_one_bottom_one
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℤ) (hr : 2≤r) (p q : ℤ × ℤ) (x : Ambient background X p) (u : Ambient background X q)
    (y : Ambient background Y p) (v : Ambient background Y q)
    (hy : y=(background.classical.map f).pageMap 2 p x)
    (hv : v=(background.classical.map f).pageMap 2 q u)
    (hd : HasDifferential (background.classical.obj (X.obj background.auxiliary)) r p q x u) :
    IsCycle background Y (r-1) p y ∧ IsCycle background Y (r-1) q v ∧
      DifferentialAt background Y r p q y v := by
  subst y; subst v
  have h : DifferentialAt background Y r p q
      ((background.classical.map f).pageMap 2 p x) ((background.classical.map f).pageMap 2 q u) :=
    ⟨hr,(background.classical.map f).hasDifferential hd⟩
  exact ⟨(cycles_of_differential Y r p q _ _ h).1,
    (cycles_of_differential Y r p q _ _ h).2,h⟩

/-- For `K₂=1` and `K₁=q+1≥2`, the source-finite theorem gives
the known-source conclusion under the upper hypotheses. -/
public theorem known_source_differential_positive_first_bottom_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+N+1,t+N))
    (z : Ambient background T.Z (s,t+1))
    (y : Ambient background T.Y (s+q+1,(t+1)+q))
    (_hFx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0)
    (hxz : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t+1) (s+q+1,(t+1)+q) z
      ((background.classical.map T.g).pageMap 2 (s+q+1,(t+1)+q) y))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (s+j,t+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (s+j,t+j) →
        ∃ z' : Ambient background T.Z (s+j,t+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (s+j,t+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+j) (t+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (s+j,t+j))
    (himage : ∀ e : Ambient background T.X (s+q,t+q),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q) e ∈
        cycles background T.Y ((N-q:ℕ)+1) (s+q+1,(t+q)+1)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+N+1) (t+N) u
    IsCycle background T.Y (N-q:ℕ) (s+q+1,(t+1)+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((s+N+1)+1,(t+N)+1) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (s+q+1,(t+1)+q)
        ((s+N+1)+1,(t+N)+1) y v := by
  exact source_finite_differential_positive_first_bottom_one
    T he hf hg hh q N hq hqN s t x u z y _hFx hxz hdx hdz hmid himage

/-- For `K₂=1` and `K₁=q+1≥2`, the source-finite theorem gives
the known-source conclusion under the upper hypotheses. -/
public theorem known_source_differential_ordinary_second_bottom_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using x))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B+1,W+1) ((B+q+1)+1,(W+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+q+1) (W+q) y))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e ∈
        cycles background T.Y ((N-q:ℕ)+1) (B+q+1,W+q)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-q:ℕ) (B+q+1,W+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (B+q+1,W+q) ((B+1)+N+1,W+N) y v := by
  exact source_finite_differential_ordinary_second_bottom_one
    T he hf hg hh q N hq hqN B W x z y hxz u _hFx hdx hdz hmid himage

/-- For `K₂=1` and `K₁=q+1≥2`, the source-finite theorem gives
the known-source conclusion under the upper hypotheses. -/
public theorem known_source_differential_ordinary_third_bottom_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using x))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B,W) (B+q+1,W+q) z
      ((background.classical.map T.g).pageMap 2 (B+q+1,W+q) y))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((B+1)+j-1+1,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) ((B+1)+j-1+1,W+j) →
        ∃ z' : Ambient background T.Z ((B+1)+j-1,W+j),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u' : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z') (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1) ((B+1)+j-1+1,W+j))
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e ∈
        cycles background T.Y ((N-q:ℕ)+1) (B+q+1,W+q)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-q:ℕ) (B+q+1,W+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (B+q+1,W+q) ((B+1)+N+1,W+N) y v := by
  exact source_finite_differential_ordinary_third_bottom_one
    T he hf hg hh q N hq hqN B W x z y hxz u _hFx hdx hdz hmid himage

end
end KIP126.ProofTools.Internal.SyntheticCoverage
