module

import all KIP126.ProofTools.SyntheticCoverage.EarlySourceTop
import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyComparison

/-! Source representative adjustment with fixed first and differential-target
labels. Each additional longer-cycle direction is lifted one quotient level
higher before truncation, preserving the actual adjacent boundary. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

/-- One source-comparison layer: an H-cycle changes only the short source
without changing its actual positive image; an additional longer cycle
changes the long source while preserving its first quotient and exact
adjacent boundary. -/
private theorem source_adjustment_positive_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (j q N : ℕ) (hj : 0<j) (hq : 0<q) (hKN : j+q≤N) (s t : ℤ)
    (hmid : ∀ x : Ambient background T.X (s,t), x ∈ cycles background T.X q (s,t) →
      ∃ z : Ambient background T.Z (s,t+1), z ∈ cycles background T.Z q (s,t+1) ∧
      ∃ k : Ambient background T.X (s,t), k ∈ cycles background T.X (N+1-j:ℕ) (s,t) ∧
        x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z-k ∈
          boundaries background T.X (j+1) (s,t))
    (R : BiHom (t-s) (t-j)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (j+q)))
    (ζ : BiHom (t-s) (t-j)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower s
      (R-ζ ≫ (background.quotients.tower _).rho (j+q) N hKN)) :
    ∃ (R' : BiHom (t-s) (t-j)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (j+q)))
      (ζ' : BiHom (t-s) (t-j)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 (j+q) (by omega)=
        R ≫ (background.quotients.tower _).rho 1 (j+q) (by omega) ∧
      positiveFiniteImage T hf (j+q) (levelQuotientShiftIso T.X 1 (j+q)) (t-s) (t-j) R'=
        positiveFiniteImage T hf (j+q) (levelQuotientShiftIso T.X 1 (j+q)) (t-s) (t-j) R ∧
      ζ' ≫ (background.quotients.tower _).rho 1 N (by omega)=
        ζ ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      ζ' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        ζ ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower (s+1)
        (R'-ζ' ≫ (background.quotients.tower _).rho (j+q) N hKN) := by
  obtain ⟨x,hxc,hxd⟩ := middle_finite_filtration_label T.X (j+q) j (by omega) s t
    (R-ζ ≫ (background.quotients.tower _).rho (j+q) N hKN) herror
  obtain ⟨z,hz,k,hk,hcong⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc)
  obtain ⟨b,hb,hbz⟩ := selective_positive_f_native_cycle_image T he hf hg hh hT j q hq s t
    (levelQuotientShiftIso T.X 1 (j+q)) (level_quotient_shift_incl T.X 1 (j+q)) z hz
    (KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z)
    (KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T s t z)
  obtain ⟨c,hc,hcf,hcd⟩ := higher_root_correction T.X N j hj (by omega) s t k hk
  have hcshort := higher_finite_restriction_detects T.X (j+q) (N+1) j (by omega) s t k c hc
  have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub
    (.quotient (j+q) (.nu T.X)) (s,t,t-j) hxd hb
  rw [←finiteTargetLabel_sub] at hsub
  have hnext := middle_finite_congruent_difference T.X (j+q) j (by omega) s t
    (x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z) k hcong
    ((R-ζ ≫ (background.quotients.tower _).rho (j+q) N hKN)-b)
    (c ≫ (background.quotients.tower _).rho (j+q) (N+1) (by omega)) hsub hcshort
  have hbfirst : b ≫ (background.quotients.tower _).rho 1 (j+q) (by omega)=0 :=
    finite_filtered_first_quotient_zero T.X (j+q) j (by omega) hj s t b
      (KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient (j+q) (.nu T.X))
        (s,t,t-j) (finiteTargetLabel background T.X (j+q) s t j
          (KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z)) b hb)
  refine ⟨R-b,ζ+c ≫ (background.quotients.tower _).rho N (N+1) (by omega),?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hbfirst,sub_zero]
  · rw [positiveFiniteImage_sub,hbz,sub_zero]
  · rw [Preadditive.add_comp,hcf,add_zero]
  · rw [Preadditive.add_comp,hcd,add_zero]
  · rw [Preadditive.add_comp,Category.assoc,(background.quotients.tower _).rho_comp]
    convert hnext using 1
    abel

private theorem source_adjustment_positive_step_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (K N j q : ℕ) (hK : K=j+q) (hj : 0<j) (hq : 0<q) (hKN : K≤N)
    (p t m w : ℤ) (hm : m=t-p) (hw : w=t-j)
    (hmid : ∀ x : Ambient background T.X (p,t), x ∈ cycles background T.X (K-j:ℕ) (p,t) →
      ∃ z : Ambient background T.Z (p,t+1), z ∈ cycles background T.Z (K-j:ℕ) (p,t+1) ∧
      ∃ k : Ambient background T.X (p,t), k ∈ cycles background T.X (N+1-j:ℕ) (p,t) ∧
        x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t z-k ∈
          boundaries background T.X (j+1) (p,t))
    (R : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K))
    (ζ : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower p
      (R-ζ ≫ (background.quotients.tower _).rho K N hKN)) :
    ∃ (R' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K))
      (ζ' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 K (by omega)=
        R ≫ (background.quotients.tower _).rho 1 K (by omega) ∧
      positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) m w R'=
        positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) m w R ∧
      ζ' ≫ (background.quotients.tower _).rho 1 N (by omega)=
        ζ ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      ζ' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        ζ ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower (p+1)
        (R'-ζ' ≫ (background.quotients.tower _).rho K N hKN) := by
  subst K; subst m; subst w
  apply source_adjustment_positive_step T he hT hf hg hh j q N hj hq hKN p t
    (by simpa only [Nat.add_sub_cancel_left] using hmid) R ζ herror

/-- All additional longer-cycle summands are removed by finite iteration.
The returned long source retains its exact first quotient and adjacent
boundary, while the returned short source retains its actual positive image. -/
private theorem source_adjustment_positive_to_last
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (K N : ℕ) (hK : 0<K) (hKN : K≤N) (m w u v : ℤ)
    (huv : u≤v) (hwindow : 0<m+u-w) (hv : v≤(K:ℤ)+w-m)
    (hmid : ∀ p : ℤ, u≤p → p<v →
      ∀ x : Ambient background T.X (p,m+p),
        x ∈ cycles background T.X (K-(m+p-w).toNat:ℕ) (p,m+p) →
        ∃ z : Ambient background T.Z (p,m+p+1),
          z ∈ cycles background T.Z (K-(m+p-w).toNat:ℕ) (p,m+p+1) ∧
        ∃ k : Ambient background T.X (p,m+p),
          k ∈ cycles background T.X (N+1-(m+p-w).toNat:ℕ) (p,m+p) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p (m+p) z-k ∈
            boundaries background T.X ((m+p-w).toNat+1) (p,m+p))
    (R : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K))
    (ζ : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower u
      (R-ζ ≫ (background.quotients.tower _).rho K N hKN)) :
    ∃ (R' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K))
      (ζ' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 K (by omega)=
        R ≫ (background.quotients.tower _).rho 1 K (by omega) ∧
      positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) m w R'=
        positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) m w R ∧
      ζ' ≫ (background.quotients.tower _).rho 1 N (by omega)=
        ζ ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      ζ' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        ζ ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower v
        (R'-ζ' ≫ (background.quotients.tower _).rho K N hKN) := by
  induction hd : (v-u).toNat using Nat.strong_induction_on generalizing u R ζ with
  | h n ih =>
    by_cases hend : v≤u
    · have huv' : u=v := le_antisymm huv hend
      exact ⟨R,ζ,rfl,rfl,rfl,rfl,huv' ▸ herror⟩
    · let j := (m+u-w).toNat
      have hj : (j:ℤ)=m+u-w := by dsimp [j]; omega
      have hjpos : 0<j := by omega
      have hjK : j<K := by omega
      obtain ⟨R₁,ζ₁,hRf,hRi,hζf,hζδ,hnext⟩ := source_adjustment_positive_step_at
        T he hT hf hg hh K N j (K-j) (by omega) hjpos (by omega) hKN
        u (m+u) m w (by omega) (by omega) (hmid u le_rfl (by omega)) R ζ herror
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨R₂,ζ₂,hRf₂,hRi₂,hζf₂,hζδ₂,hfinal⟩ :=
        ih (v-(u+1)).toNat hd' (u+1) (by omega) (by omega)
          (fun p hp hpv => hmid p (by omega) hpv) R₁ ζ₁ hnext rfl
      exact ⟨R₂,ζ₂,hRf₂.trans hRf,hRi₂.trans hRi,hζf₂.trans hζf,hζδ₂.trans hζδ,hfinal⟩

private theorem source_adjustment_boundary_label_eq
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (hN : 0<N) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hδ : a ≫ ((background.quotients.tower _).triangle hN (Nat.lt_succ_self N)).delta=
      b ≫ ((background.quotients.tower _).triangle hN (Nat.lt_succ_self N)).delta) :
    adjacentBoundaryLabel X N s t a=adjacentBoundaryLabel X N s t b := by
  rw [←adjacentFiniteBoundary_eq X N hN s t a,←adjacentFiniteBoundary_eq X N hN s t b]
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have transport (n : ℕ) (hn : n=1)
      (δ : XModLambdaN A N ⟶ ((SyntheticCategory.biShift (0,-(N:ℤ))).obj
        (XModLambdaN A n))⟦(1:ℤ)⟧)
      (e : (XModLambdaN A N ⟶ ((SyntheticCategory.biShift (0,-(N:ℤ))).obj
        (XModLambdaN A n))⟦(1:ℤ)⟧)=
        (XModLambdaN A N ⟶ ((SyntheticCategory.biShift (0,-(N:ℤ))).obj
          (XModLambdaN A 1))⟦(1:ℤ)⟧))
      (hd : a ≫ δ=b ≫ δ) : a ≫ e.mp δ=b ≫ e.mp δ := by
    subst n
    cases e
    exact hd
  have h := transport (N+1-N) (by omega) _ (by rw [show N+1-N=1 by omega]) hδ
  have H := congrArg (fun z => homotopyRegrade
    (show (t-s)-1=(t+N)-(s+N+1) by omega) rfl
    (biSuspensionHomEquiv (t-s) t N (XModLambdaN A 1) z)) h
  exact H

/-- The source-adjustment variant of the early finite comparison.
Additional longer-cycle directions are allowed. The new long source retains
the first label and differential-target label, and its corrected positive
image has the original top plus an F₂ error. -/
private theorem source_adjustment_positive_finite_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q N : ℕ) (hq : 0<q) (hqN : q+1≤N) (S V : ℤ)
    (v : Ambient background T.Y (S+q+1,V+q+1))
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
        ∃ k : Ambient background T.X (S+j,V+j),
          k ∈ cycles background T.X (N+1-j:ℕ) (S+j,V+j) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z-k ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (cA : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (ζ : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hfirst : cA ≫ (background.quotients.tower _).rho 1 (q+1) (by omega)=
      ζ ≫ (background.quotients.tower _).rho 1 N (by omega))
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : positiveFiniteImage T hf (q+1) (levelQuotientShiftIso T.X 1 (q+1)) (V-S) V cA=
      W ≫ XModLambdaN.incl _ (q+1)+
        homotopyRegrade (show (V+q+1)-(S+q+1)=V-S by omega) rfl
          (finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) (V+q+1) (V+1) (by omega) v)) :
    ∃ ζ' : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      ζ' ≫ (background.quotients.tower _).rho 1 N (by omega)=
        ζ ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      adjacentBoundaryLabel T.X N S V ζ'=adjacentBoundaryLabel T.X N S V ζ ∧
      ∃ e : Ambient background T.X (S+q,V+q),
        homotopyRegrade (show V-S=(V+q+1)-(S+q+1) by omega) rfl
          ((positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V ζ'-
            W ≫ XModLambdaN.incl _ N) ≫ (background.quotients.tower _).rho (q+1) N hqN)=
          finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) (V+q+1) (V+1) (by omega)
            (v+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (V+q) e) := by
  have herror : FiltrationAtLeast background.syntheticTower (S+1)
      (cA-ζ ≫ (background.quotients.tower _).rho (q+1) N hqN) := by
    apply finite_first_kernel_filtration T.X (q+1) (by omega) S V
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_comp,hfirst,sub_self]
  obtain ⟨R,ζ',_,hRi,hζf,hζδ,hfinal⟩ := source_adjustment_positive_to_last
    T he hT hf hg hh (q+1) N (by omega) hqN (V-S) V (S+1) (S+q)
    (by omega) (by omega) (by omega) (by
      intro p hp hpq x hx
      let j := (p-S).toNat
      have hj : (j:ℤ)=p-S := by dsimp [j]; omega
      have hi : (V-S+p-V).toNat=j := by dsimp [j]; congr 1; omega
      have hs : S+j=p := by omega
      have ht : V+j=V-S+p := by omega
      have H := hmid j (by omega) (by omega)
      rw [hs,ht] at H
      rw [hi]
      have hc : (((q+1-j:ℕ):ℤ))=((q+1:ℕ):ℤ)-j := by omega
      simpa only [hc,Nat.cast_add,Nat.cast_one] using H x (by simpa only [hi,hc] using hx)) cA ζ herror
  let a := ζ' ≫ (background.quotients.tower _).rho (q+1) N hqN-R
  have haf : FiltrationAtLeast background.syntheticTower (S+q) a := by
    have hn := (background.syntheticTower.filtrationSubmodule _ (S+q) (V-S,V)).neg_mem hfinal
    simpa only [a,neg_sub,FiltrationAtLeast] using hn
  let a' := homotopyRegrade (show V-S=(V+q)-(S+q) by omega) rfl a
  have ha' : FiltrationAtLeast background.syntheticTower (S+q) a' :=
    (regrade_filtration_iff _ _ _ a).mpr haf
  obtain ⟨e,heTop⟩ := last_layer_positive_image_eq_top_at_weight T hf q (q+1) hq rfl
    (S+q) (V+q) V (by omega) (levelQuotientShiftIso T.X 1 (q+1))
    (level_quotient_shift_incl T.X 1 (q+1)) a' ha'
  have heTop' : homotopyRegrade (show V-S=(V+q+1)-(S+q+1) by omega) rfl
      (positiveFiniteImage T hf (q+1) (levelQuotientShiftIso T.X 1 (q+1)) (V-S) V a)=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) (V+q+1) (V+1) (by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (V+q) e) := by
    simpa only [a',←positiveFiniteImage_regrade,normalized_homotopy_regrade_trans] using heTop
  refine ⟨ζ',hζf,source_adjustment_boundary_label_eq T.X N (by omega) S V ζ' ζ hζδ,e,?_⟩
  have hsum : (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V ζ'-
        W ≫ XModLambdaN.incl _ N) ≫ (background.quotients.tower _).rho (q+1) N hqN=
      homotopyRegrade (show (V+q+1)-(S+q+1)=V-S by omega) rfl
        (finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) (V+q+1) (V+1) (by omega) v)+
      positiveFiniteImage T hf (q+1) (levelQuotientShiftIso T.X 1 (q+1)) (V-S) V a := by
    dsimp only [a]
    rw [positiveFiniteImage_sub,hRi,hcAi,Preadditive.sub_comp,
      positive_finite_image_restriction T hf (q+1) N (by omega) hqN,
      Category.assoc,(background.quotients.tower _).rho_quotient]
    abel
  rw [hsum,regrade_add,normalized_homotopy_regrade_trans,top_target_regrade_self,heTop',
    finite_top_label_at_weight_add]

/-- The adjusted-source comparison at the original short quotient length
and target degree. The specified candidate vector is retained verbatim. -/
private theorem source_adjustment_positive_finite_top_at_degree
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q K N : ℕ) (hq : 0<q) (hK : K=q+1) (hKN : K≤N)
    (S V A B : ℤ) (hA : A=S+q+1) (hB : B=V+q+1)
    (v : Ambient background T.Y (A,B))
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
        ∃ k : Ambient background T.X (S+j,V+j),
          k ∈ cycles background T.X (N+1-j:ℕ) (S+j,V+j) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z-k ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (cA : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K))
    (ζ : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hfirst : cA ≫ (background.quotients.tower _).rho 1 K (by omega)=
      ζ ≫ (background.quotients.tower _).rho 1 N (by omega))
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) (V-S) V cA=
      W ≫ XModLambdaN.incl _ K+
        homotopyRegrade (show B-A=V-S by omega) rfl
          (finiteTopLabelAtWeight T.Y q hq K (by omega) A B (V+1) (by omega) v)) :
    ∃ ζ' : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      ζ' ≫ (background.quotients.tower _).rho 1 N (by omega)=
        ζ ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      adjacentBoundaryLabel T.X N S V ζ'=adjacentBoundaryLabel T.X N S V ζ ∧
      ∃ e : Ambient background T.X (S+q,V+q), ∃ error : Ambient background T.Y (A,B),
        HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (V+q) e) ∧
        homotopyRegrade (show V-S=B-A by omega) rfl
          ((positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V ζ'-
            W ≫ XModLambdaN.incl _ N) ≫ (background.quotients.tower _).rho K N hKN)=
          finiteTopLabelAtWeight T.Y q hq K (by omega) A B (V+1) (by omega) (v+error) := by
  subst K; subst A; subst B
  obtain ⟨ζ',hζf,hζδ,e,htop⟩ := source_adjustment_positive_finite_top
    T he hT hf hg hh q N hq hKN S V v hmid cA ζ hfirst W hcAi
  exact ⟨ζ',hζf,hζδ,e,_,HEq.rfl,htop⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
