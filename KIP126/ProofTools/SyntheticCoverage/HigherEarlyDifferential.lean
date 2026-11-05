module

public import KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyComparison
import all KIP126.ProofTools.SyntheticCoverage.EarlyTargetDifferential

/-! Higher early-boundary target differentials. The same chosen main source
is retained while its positive image is corrected by the actual earlier
absolute boundary. -/

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
set_option maxHeartbeats 1000000

/-- The same main lift is selected with the corrected specified target,
then its positive image is corrected by the actual Q_i absolute boundary.
The first label and the exact full boundary F(U)-W are both retained. -/
private theorem higher_positive_corrected_source
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (L i : ℕ) (hi : 0 < i) (hiL : i<L) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u u' : Ambient background T.X (s+L+1,t+L))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hu : u'-u∈boundaries background T.X (i+1) (s+L+1,t+L))
    (aHat : BiHom (((t+L)-(s+L+1))+1) (((t+L)+1)-i)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i))
    (W : BiHom ((t+L)-(s+L+1)) ((t+L)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hW : W=homotopyRegrade (show (((t+L)-(s+L+1))+1)-1=(t+L)-(s+L+1) by omega)
        (show (((t+L)+1)-i)+i=(t+L)+1 by omega)
        (biSuspensionHomEquiv (((t+L)-(s+L+1))+1) (((t+L)+1)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ i))) :
    ∃ ζ : BiHom (t-s) t
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) L),
      ζ ≫ (background.quotients.tower _).rho 1 L (by omega)=nativeFirstLabel T.X s t x ∧
      positiveAdjustedBoundary T.X L s t ζ ≫ XModLambdaN.incl _ 1=
        nativeFirstLabel T.X (s+L+1) (t+L) u' ∧
      ∃ ξ : BiHom (t-s) (t+1)
          (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L),
        homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
            (ξ ≫ (background.quotients.tower _).rho 1 L (by omega)) =
          nativeFirstLabel T.Y (s+1) (t+1)
            (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
        homotopyRegrade (show (t-s)-1=(t+L)-(s+L+1) by omega)
            (show (t+1)+L=(t+L)+1 by omega)
            (biSuspensionHomEquiv (t-s) (t+1) L
              (background.nu.functor.obj (T.Y.obj background.auxiliary)) (ξ ≫ XModLambdaN.proj _ L)) =
          (verticalTranslate _ 1 ((t+L)-(s+L+1)) (t+L)
            (positiveAdjustedBoundary T.X L s t ζ) ≫ lastLayerNormalizedMap T hf)-W := by
  have hd' := differential_of_earlier_boundaries T.X (L+1) (i+1) (i+1)
    (s,t) (s+L+1,t+L) x x u u' ⟨by omega,hdx⟩ (by omega) (by omega)
    (by rw [sub_self]; exact (boundaries background T.X (i+1) (s,t)).zero_mem) hu
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega) s t x u').mp hd'.2
  refine ⟨ζ,hζ,(positive_adjusted_boundary_first T.X L s t ζ).trans hU,?_⟩
  let a₀ := homotopyRegrade (show ((t+L)-(s+L+1))+1=t-s by omega)
    (show ((t+L)+1)-i=(t+1)+L-i by omega) aHat
  obtain ⟨ξ,hξ,hξb⟩ := positive_source_correction_of_earlier_boundary T hf L i hi hiL s t x ζ hζ a₀
  refine ⟨ξ,hξ,?_⟩
  have haW : homotopyRegrade (show (t-s)-1=(t+L)-(s+L+1) by omega)
      (show (((t+1)+L-i)+i)=(t+L)+1 by omega)
      (biSuspensionHomEquiv (t-s) ((t+1)+L-i) i
        (background.nu.functor.obj (T.Y.obj background.auxiliary)) (a₀ ≫ XModLambdaN.proj _ i)) = W := by
    dsimp only [a₀]
    rw [←regrade_comp,early_bi_susp_regrade,normalized_homotopy_regrade_trans]
    exact hW.symm
  erw [haW] at hξb
  exact hξb

private theorem higher_positive_compatible_finite_lift_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i d : ℕ) (hi : 0 < i) (hdpos : 0<d) (s t S V : ℤ) (hS : S=s+i) (hV : V=t+i-1)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (S,V))
    (v : Ambient background T.Y (s+(i+d)+1,t+(i+d)))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) (s,t) (s+(i+d)+1,t+(i+d)) ((background.classical.map T.g).pageMap 2 (s,t) c) ((background.classical.map T.g).pageMap 2 (s+(i+d)+1,t+(i+d)) v))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c
      (boundaryLabelRegrade (show S+1=s+i+1 by omega) (show V+1=t+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf S V u)))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z ((i+d)+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (S,V+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T S V z ∈
        boundaries background T.X (i+1) (S,V)) :
    let K : ℕ := d+1
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K),
    ∃ u' : Ambient background T.X (S,V),
    ∃ aHat : BiHom ((V-S)+1) ((V+1)-i)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b ≫ (background.quotients.tower _).rho 1 K (by dsimp [K]; omega)=nativeFirstLabel T.X S V u' ∧
      u'-u ∈ boundaries background T.X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega)
        (show ((V+1)-i)+i=V+1 by omega)
        (biSuspensionHomEquiv ((V-S)+1) ((V+1)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) (V-S) V b=
        W ≫ XModLambdaN.incl _ K+
          homotopyRegrade (show (t+(i+d))-(s+(i+d)+1)=V-S by omega) rfl
            (finiteTopLabelAtWeight T.Y d (by omega) K (by rfl)
              (s+(i+d)+1) (t+(i+d)) (V+1) (by omega) v) := by
  subst S
  subst V
  have h := higher_positive_compatible_finite_lift T he hT hf hg hh i (i+d) hi (by omega)
    s t c u v hd hearly hR hH
  let R (n : ℕ) (hn : n=0+((i+d-i)+1)) : Prop :=
    ∃ b : BiHom ((t+i-1)-(s+i)) (t+i-1)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) n),
    ∃ u' : Ambient background T.X (s+i,t+i-1),
    ∃ aHat : BiHom (((t+i-1)-(s+i))+1) (((t+i-1)+1)-i)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom ((t+i-1)-(s+i)) ((t+i-1)+1)
        (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b ≫ (background.quotients.tower _).rho 1 n (by omega)=nativeFirstLabel T.X (s+i) (t+i-1) u' ∧
      u'-u ∈ boundaries background T.X (i+1) (s+i,t+i-1) ∧
      W=homotopyRegrade (show (((t+i-1)-(s+i))+1)-1=(t+i-1)-(s+i) by omega)
        (show (((t+i-1)+1)-i)+i=(t+i-1)+1 by omega)
        (biSuspensionHomEquiv (((t+i-1)-(s+i))+1) (((t+i-1)+1)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      positiveFiniteImage T hf n (levelQuotientShiftIso T.X 1 n) ((t+i-1)-(s+i)) (t+i-1) b=
        W ≫ XModLambdaN.incl _ n+
          homotopyRegrade (show (t+(i+d))-(s+(i+d)+1)=(t+i-1)-(s+i) by omega) rfl
            (finiteTopLabelAtWeight T.Y (i+d-i) (by omega) n (by omega)
              (s+(i+d)+1) (t+(i+d)) ((t+i-1)+1) (by omega) v)
  have hr : R (i+d+1-i) (by omega) := h
  have transport (n : ℕ) (hn : n=0+((i+d-i)+1)) (hn' : n=d+1)
      (hh : R n hn) : R (d+1) (by omega) := by
    cases hn'
    exact hh
  have hr' := transport (i+d+1-i) (by omega) (by omega) hr
  dsimp only [R] at hr'
  simpa only [Nat.add_sub_cancel_left] using hr'


/-- Higher early-boundary target transfer for a positive first arrow. The main
page is L+1, the early page i+1, the root page i+d+1, and the constructed
output page L+d+1. -/
private theorem differential_of_higher_early_boundary_positive
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L i d : ℕ) (hi : 0 < i) (hiL : i<L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y ((s+L+1-i),(t+L+1-i)))
    (v : Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+i+1,(t+L+1-i)+i) c
      (boundaryLabelRegrade (show (s+L+1)+1=(s+L+1-i)+i+1 by omega)
        (show (t+L)+1=(t+L+1-i)+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u)))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i),(t+L+1-i)) c)
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v))
    (hR : ∀ p : ℤ, (s+L+1-i)+1≤p → p<(s+L+1-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), z ∈ cycles background T.Z ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) →
      ∃ y : Ambient background T.Y (p,(t+L+1-i)-(s+L+1-i)+p), y ∈ cycles background T.Y ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
      ∃ k : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), k ∈ cycles background T.Z ((i+d)+1-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,(t+L+1-i)-(s+L+1-i)+p) y-k ∈
          boundaries background T.Z ((p-(s+L+1-i)).toNat+1) (p,(t+L+1-i)-(s+L+1-i)+p))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X (i+1) (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))))
    (hP : permanentCycles background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))) :
    IsCycle background T.Y (L+d) (s+1,t+1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
    IsCycle background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,u',aHat,W,hcA,hu',hW,_,hcAi⟩ := higher_positive_compatible_finite_lift_at
    T he hT hf hg hh i d hi hd (s+L+1-i) (t+L+1-i) (s+L+1) (t+L) (by omega) (by omega)
    c u v hdz hearly hR hH
  obtain ⟨ζ,hζ,hU,ξ,hξ,hξb⟩ := higher_positive_corrected_source T hf L i hi hiL s t x u u' hdx hu' aHat W hW
  obtain ⟨e,error,herror,htop⟩ := early_positive_selective_top_at_degree T he hT hf hg hh
    d (d+1) hd (by omega) (s+L+1) (t+L)
    ((s+L+1-i)+(i+d)+1) ((t+L+1-i)+(i+d)) (by omega) (by omega) u' v
    Pm hPm hmid (positiveAdjustedBoundary T.X L s t ζ) hU cA hcA W hcAi
  have heG : (background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) error=0 := by
    have hgF := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh ((s+L+1)+d) ((t+L)+d)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+d) ((t+L)+d) e)).mpr ⟨e,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'
      simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by ext <;> dsimp <;> omega) _ _ herror hgF
  let ξY := homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl ξ
  have hξY : ξY ≫ (background.quotients.tower _).rho 1 L (by omega)=
      nativeFirstLabel T.Y (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) := by
    simpa only [ξY,←regrade_comp] using hξ
  have hfinalTop : homotopyRegrade
      (show ((t+1)-(s+1))-1=((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1) by omega)
      (show (t+1)+L=((t+L+1-i)+(i+d))-d by omega)
      (biSuspensionHomEquiv ((t+1)-(s+1)) (t+1) L
        (background.nu.functor.obj (T.Y.obj background.auxiliary)) (ξY ≫ XModLambdaN.proj _ L) ≫
          XModLambdaN.incl _ (d+1)) =
      finiteTopLabel T.Y d hd ((s+L+1-i)+(i+d)+1) ((t+L+1-i)+(i+d)) (v+error) := by
    have hb := congrArg (fun b => b ≫ XModLambdaN.incl
      (background.nu.functor.obj (T.Y.obj background.auxiliary)) (d+1)) hξb
    have hb' := congrArg (homotopyRegrade
      (show (t+L)-(s+L+1)=((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1) by omega) rfl) hb
    rw [←regrade_comp,normalized_homotopy_regrade_trans] at hb'
    have ht := hb'.trans htop
    have ht' := congrArg (homotopyRegrade (rfl :
        ((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1)=((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1))
      (show (t+L)+1=((t+L+1-i)+(i+d))-d by omega)) ht
    convert ht' using 1 <;>
      simp only [ξY,←regrade_comp,early_bi_susp_regrade,normalized_homotopy_regrade_trans,
        finiteTopLabelAtWeight,top_target_regrade_self]
  exact early_target_of_retained_boundary_top_at_degree T.Y T.Z T.g L d (by omega) hd
    (s+1) (t+1) ((s+L+1-i)+(i+d)+1) ((t+L+1-i)+(i+d)) (by omega) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v error P hP hv hker heG ξY hξY hfinalTop


/-- Original displayed-page-source form of the higher early-boundary target theorem. The original F_r[x]=[y] relation is retained as the exact B_<r coset, and both output cycle statements are derived. -/
public theorem differential_of_higher_early_boundary_positive_page_source
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L i d : ℕ) (hi : 0 < i) (hiL : i<L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (y : Ambient background T.Y (s+1,t+1))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y ((s+L+1-i),(t+L+1-i)))
    (v : Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+i+1,(t+L+1-i)+i) c
      (boundaryLabelRegrade (show (s+L+1)+1=(s+L+1-i)+i+1 by omega)
        (show (t+L)+1=(t+L+1-i)+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u)))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i),(t+L+1-i)) c)
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v))
    (hR : ∀ p : ℤ, (s+L+1-i)+1≤p → p<(s+L+1-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), z ∈ cycles background T.Z ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) →
      ∃ y : Ambient background T.Y (p,(t+L+1-i)-(s+L+1-i)+p), y ∈ cycles background T.Y ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
      ∃ k : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), k ∈ cycles background T.Z ((i+d)+1-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,(t+L+1-i)-(s+L+1-i)+p) y-k ∈
          boundaries background T.Z ((p-(s+L+1-i)).toNat+1) (p,(t+L+1-i)-(s+L+1-i)+p))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X (i+1) (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))))
    (hP : permanentCycles background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)))
    (hy : y-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y L (s+1,t+1)) :
    IsCycle background T.Y (L+d) (s+1,t+1)
      y ∧
    IsCycle background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      y v := by
  have hdiff := differential_of_higher_early_boundary_positive T he hf hg hh L i d hi hiL hd s t
    x u c v hdx hearly hdz hR hH Pm hPm hmid P hP hv hker
  have hfinal := early_target_of_page_source T.Y (L+d+1) L (s+1,t+1)
    ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) y v hdiff.2.2 hy
  simpa only [add_sub_cancel_right] using hfinal

end
end KIP126.ProofTools.Internal.SyntheticCoverage
