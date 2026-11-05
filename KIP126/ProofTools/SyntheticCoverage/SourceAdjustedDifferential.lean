module

import all KIP126.ProofTools.SyntheticCoverage.HigherEarlySource
import all KIP126.ProofTools.SyntheticCoverage.SourceRepresentativeAdjustment

/-! Source early-boundary criteria with adjustment of the main finite
representative. The actual first label and adjacent boundary label are
preserved, while the full absolute boundary is allowed to change.
-/

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

/-- The compatible finite construction holds under the larger middle
spaces allowing long-cycle adjustments of the main source. The output keeps
the literal original target, by the actual adjacent boundary comparison. -/
private theorem source_adjusted_differential_of_compatible_finite_lift
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (d K N : ℕ) (hd : 0<d) (hK : K=d+1) (hKN : K≤N)
    (S V A B b : ℤ) (hA : A=S+d+1) (hB : B=V+d+1)
    (x x' : Ambient background T.X (S,V)) (u : Ambient background T.X (S+N+1,V+N))
    (y : Ambient background T.Y (A,B))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (S,V) (S+N+1,V+N) x u)
    (hxx : x'-x ∈ boundaries background T.X b (S,V))
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
        ∃ k : Ambient background T.X (S+j,V+j),
          k ∈ cycles background T.X (N+1-j:ℕ) (S+j,V+j) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z-k ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (cA : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K))
    (hcA : cA ≫ (background.quotients.tower _).rho 1 K (by omega)=nativeFirstLabel T.X S V x')
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) (V-S) V cA=
      W ≫ XModLambdaN.incl _ K+
        homotopyRegrade (show B-A=V-S by omega) rfl
          (finiteTopLabelAtWeight T.Y d hd K (by omega) A B (V+1) (by omega) y))
    (himage : ∀ e : Ambient background T.X (S+d,V+d),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+d) (V+d) e ∈
        cycles background T.Y ((N-d:ℕ)+1) (S+d+1,V+d+1)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+N+1) (V+N) u
    IsCycle background T.Y (N-d:ℕ) (A,B) y ∧
      IsCycle background T.Y (N-d:ℕ) ((S+N+1)+1,(V+N)+1) v ∧
      DifferentialAt background T.Y ((N-d:ℕ)+1) (A,B) ((S+N+1)+1,(V+N)+1) y v := by
  subst K; subst A; subst B
  have hdx' := differential_of_source_boundary_congruent T.X (N+1) b
    (S,V) (S+N+1,V+N) x' x u hdx hxx
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega)
    S V x' u).mp hdx'
  obtain ⟨ζ',hfirst,hboundary,e,htop⟩ := source_adjustment_positive_finite_top
    T he hT hf hg hh d N hd hKN S V y hmid cA ζ (hcA.trans hζ.symm) W hcAi
  exact higher_source_differential_of_corrected_top T hf d (d+1) N hd rfl hKN
    S V (S+d+1) (V+d+1) rfl (by omega) u y _ ζ' (hboundary.trans hU) W htop (himage e)


/-- Source early-boundary transfer with the weaker middle spaces admitting
long cycles of the original main differential. This is the source-adjustment
variant of the d₂ criterion; the original y and F₂u are preserved. -/
private theorem source_adjusted_early_differential_positive_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q N : ℕ) (hq : 2≤q) (hqN : q≤N) (s t : ℤ)
    (x : Ambient background T.X (s+1,t))
    (u : Ambient background T.X ((s+1)+N+1,t+N))
    (c : Ambient background T.Y (s,t))
    (y : Ambient background T.Y (s+q+1,t+q))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s+1,t) ((s+1)+N+1,t+N) x u)
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q)
      ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) y))
    (hd₂ : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) t x))
    (hH : ∀ z : Ambient background T.Z (s+1,t+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+1) t z ∈
        boundaries background T.X 2 (s+1,t))
    (hmid : ∀ j : ℕ, 1≤j → j<q-1 →
      ∀ a : Ambient background T.X ((s+1)+j,t+j),
        a ∈ cycles background T.X ((q:ℤ)-j) ((s+1)+j,t+j) →
        ∃ z : Ambient background T.Z ((s+1)+j,t+j+1),
          z ∈ cycles background T.Z ((q:ℤ)-j) ((s+1)+j,t+j+1) ∧
        ∃ k : Ambient background T.X ((s+1)+j,t+j),
          k ∈ cycles background T.X (N+1-j:ℕ) ((s+1)+j,t+j) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+1)+j) (t+j) z-k ∈
            boundaries background T.X ((j:ℤ)+1) ((s+1)+j,t+j))
    (himage : ∀ e : Ambient background T.X ((s+1)+(q-1:ℕ),t+(q-1:ℕ)),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+1)+(q-1:ℕ)) (t+(q-1:ℕ)) e ∈
        cycles background T.Y ((N-(q-1):ℕ)+1) (((s+1)+(q-1:ℕ))+1,(t+(q-1:ℕ))+1)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+1)+N+1) (t+N) u
    IsCycle background T.Y (N-(q-1):ℕ) (s+q+1,t+q) y ∧
      IsCycle background T.Y (N-(q-1):ℕ) (((s+1)+N+1)+1,(t+N)+1) v ∧
      DifferentialAt background T.Y ((N-(q-1):ℕ)+1) (s+q+1,t+q)
        (((s+1)+N+1)+1,(t+N)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,x',aHat,W,hcA,hxx,hW,hW0,hcAi⟩ :=
    early_positive_compatible_finite_lift T he hT hf hg hh q hq s t c x y hdroot hH hd₂
  have hq' : q-1+1=q := by omega
  exact source_adjusted_differential_of_compatible_finite_lift
    T he hT hf hg hh (q-1) ((q+1)-1) N (by omega) (by omega) (by omega)
    (s+1) t (s+q+1) (t+q) 2 (by omega) (by omega) x x' u y hdx hxx
    (by simpa only [hq'] using hmid) cA hcA W hcAi himage

/-- Higher source early-boundary transfer with representative adjustment.
The root comparison uses every R_j direction, and long cycles
control the main-source comparison. -/
private theorem source_adjusted_higher_early_differential_positive_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q N : ℕ) (hi : 0 < i) (hiq : i < q) (hKN : (q+1)-i ≤ N) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (x : Ambient background T.X (s+i,t+i-1))
    (u : Ambient background T.X ((s+i)+N+1,(t+i-1)+N))
    (y : Ambient background T.Y (s+q+1,t+q))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s+i,t+i-1) ((s+i)+N+1,(t+i-1)+N) x u)
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q)
      ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) y))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c
      (boundaryLabelRegrade rfl (show (t+i-1)+1=t+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+i) (t+i-1) x)))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y' : Ambient background T.Y (p,t-s+p), y' ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y'-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+i,(t+i-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+i) (t+i-1) z ∈
        boundaries background T.X (i+1) (s+i,t+i-1))
    (hmid : ∀ j : ℕ, 1≤j → j<((q+1)-i)-1 →
      ∀ a : Ambient background T.X ((s+i)+j,(t+i-1)+j),
        a ∈ cycles background T.X (((q+1-i:ℕ):ℤ)-j) ((s+i)+j,(t+i-1)+j) →
        ∃ z : Ambient background T.Z ((s+i)+j,(t+i-1)+j+1),
          z ∈ cycles background T.Z (((q+1-i:ℕ):ℤ)-j) ((s+i)+j,(t+i-1)+j+1) ∧
        ∃ k : Ambient background T.X ((s+i)+j,(t+i-1)+j),
          k ∈ cycles background T.X (N+1-j:ℕ) ((s+i)+j,(t+i-1)+j) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+i)+j) ((t+i-1)+j) z-k ∈
            boundaries background T.X ((j:ℤ)+1) ((s+i)+j,(t+i-1)+j))
    (himage : ∀ e : Ambient background T.X ((s+i)+(q-i:ℕ),(t+i-1)+(q-i:ℕ)),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+i)+(q-i:ℕ)) ((t+i-1)+(q-i:ℕ)) e ∈
        cycles background T.Y ((N-(q-i):ℕ)+1)
          (((s+i)+(q-i:ℕ))+1,((t+i-1)+(q-i:ℕ))+1)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
      T hf ((s+i)+N+1) ((t+i-1)+N) u
    IsCycle background T.Y (N-(q-i):ℕ) (s+q+1,t+q) y ∧
      IsCycle background T.Y (N-(q-i):ℕ) (((s+i)+N+1)+1,((t+i-1)+N)+1) v ∧
      DifferentialAt background T.Y ((N-(q-i):ℕ)+1) (s+q+1,t+q)
        (((s+i)+N+1)+1,((t+i-1)+N)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,x',aHat,W,hcA,hxx,hW,hW0,hcAi⟩ :=
    higher_positive_compatible_finite_lift T he hT hf hg hh i q hi hiq s t c x y hdroot hearly hR hH
  have hK : q-i+1=q+1-i := by omega
  exact source_adjusted_differential_of_compatible_finite_lift
    T he hT hf hg hh (q-i) ((q+1)-i) N (by omega) (by omega) hKN
    (s+i) (t+i-1) (s+q+1) (t+q) (i+1) (by omega) (by omega) x x' u y hdx hxx
    (by simpa only [hK] using hmid) cA hcA W hcAi himage

end
end KIP126.ProofTools.Internal.SyntheticCoverage
