module

import all KIP126.ProofTools.SyntheticCoverage.EarlyBoundaryDifferential
import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDifferential
import all KIP126.ProofTools.SyntheticCoverage.SelectiveHead
import all KIP126.ProofTools.SyntheticCoverage.EarlySelectiveTop

/-! Finite source comparison for the source early-boundary criterion.
The construction retains the long source and full early boundary,
using the complete middle conditions. -/

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

/-- Middle elimination on a native finite source, reflecting equality
of raw images through their zero difference. -/
private theorem early_positive_native_middle_residual
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (hεp : XModLambdaN.incl _ (c+K) ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+K)))
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1) a) :
    ∃ e : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1) e ∧
      positiveFiniteImage T hf (c+K) εp (V-S) (V-c) e =
        positiveFiniteImage T hf (c+K) εp (V-S) (V-c) a := by
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) (c+K)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨raw,hraw⟩ := raw_may_source_desuspend_surjective T he hf (c+K) c S V ε a
  have hrawfil := raw_may_source_desuspend_reflects_filtration T he hf (c+K) c S V
    (S+1) ε raw (by rw [hraw]; exact ha)
  obtain ⟨e,hefil,hei⟩ := middle_normalized_residual_same_image T he hf hg hh hT
    c K hK S V hmid raw hrawfil
  refine ⟨rawMaySourceDesuspend T he hf (c+K) c S V ε e,
    raw_may_source_desuspend_preserves_filtration T he hf (c+K) c S V (S+K-1) ε e hefil,?_⟩
  have hz := selective_raw_positive_image_zero_implies_native_zero T he hf (c+K) c
    (by omega) S V ε εp hε hεp (e-raw) (by rw [Preadditive.sub_comp,hei,sub_self])
  rw [raw_may_source_desuspend_sub,positiveFiniteImage_sub,hraw] at hz
  exact sub_eq_zero.mp hz

private theorem source_top_regrade_sub {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a b : BiHom m w A) :
    homotopyRegrade hm hw (a-b)=homotopyRegrade hm hw a-homotopyRegrade hm hw b := by
  subst m'; subst w'; rfl

/-- The same finite source is compared with the compatible early lift.
The full middle conditions remove their entire difference except for an
actual last-layer first-arrow image. -/
private theorem early_positive_same_finite_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q : ℕ) (hq : 0 < q) (S V : ℤ)
    (u : Ambient background T.X (S,V))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (aNative : BiHom (V-S) V
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (0+(q+1))))
    (hNative : aNative ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) =
      nativeFirstLabel T.X S V u)
    (cA : BiHom (V-S) (V-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (0+(q+1))))
    (hcA : cA ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) =
      homotopyRegrade rfl (by omega) (nativeFirstLabel T.X S V u))
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega)
        (positiveFiniteImage T hf (0+(q+1)) (levelQuotientShiftIso T.X 1 (0+(q+1)))
          (V-S) (V-(0:ℕ)) cA) =
      homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show V+1=(V+1)-(0:ℕ) by omega) (W ≫ XModLambdaN.incl _ (0+(q+1))) +
        finiteMayTopLabel T.Y 0 q hq S (V+1) v) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (S+q+1,(V+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=((V+1)+q)-(S+q+1) by omega) rfl
        (positiveFiniteImage T hf (0+(q+1)) (levelQuotientShiftIso T.X 1 (0+(q+1)))
          (V-S) V aNative-W ≫ XModLambdaN.incl _ (0+(q+1))) =
        finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
          (S+q+1) ((V+1)+q) (V+1) (by omega) (v+error) := by
  let N := 0+(q+1)
  let ε := levelQuotientShiftIso T.X 1 N
  have hε := level_quotient_shift_incl T.X 1 N
  let a₀ : BiHom (V-S) (V-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    homotopyRegrade rfl (by omega) aNative
  have hdet := first_label_detects_unshifted T.X N (by dsimp [N]; omega)
    S V u _ hNative
  rw [←zero_weight_label] at hdet
  have ha₀ := finite_weight_detection_regrade T.X N S V V (V-(0:ℕ))
    (by omega) (by dsimp [N]; omega) (by dsimp [N]; omega) u _ hdet
  rw [finite_coefficient_weight_label] at ha₀
  let a := cA
  have hafirst : homotopyRegrade rfl (show V-(0:ℕ)=V by omega) cA ≫
      (background.quotients.tower _).rho 1 N (by dsimp [N]; omega) = nativeFirstLabel T.X S V u := by
    rw [←regrade_comp,hcA,normalized_homotopy_regrade_trans,top_target_regrade_self]
  have hadet := first_label_detects_unshifted T.X N (by dsimp [N]; omega)
    S V u _ hafirst
  rw [←zero_weight_label] at hadet
  have ha := finite_weight_detection_regrade T.X N S V V (V-(0:ℕ))
    (by omega) (by dsimp [N]; omega) (by dsimp [N]; omega) u _ hadet
  rw [finite_coefficient_weight_label,normalized_homotopy_regrade_trans,top_target_regrade_self] at ha
  have hres := detects_sub_filtration (background.convergence (.quotient N (.nu T.X)))
    (S,V,V-(0:ℕ)) ha₀ ha
  let f := positiveFiniteImage T hf N ε (V-S) (V-(0:ℕ))
  let W' := homotopyRegrade (rfl : V-S=V-S) (show V+1=(V-(0:ℕ))+1 by omega) W
  let top := f a-W' ≫ XModLambdaN.incl _ N
  have htopv : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) top =
      finiteMayTopLabel T.Y 0 q hq S (V+1) v := by
    dsimp only [top,f,a,ε,W']
    rw [source_top_regrade_sub,←regrade_comp,normalized_homotopy_regrade_trans,hcAi,add_sub_cancel_left]
  obtain ⟨e,hefil,hei⟩ := early_positive_native_middle_residual
    T he hf hg hh hT 0 (q+1) (by omega) S V
    (by simpa only [Nat.cast_zero,zero_add] using hmid) ε hε (a₀-a) hres
  have hefil' : FiltrationAtLeast background.syntheticTower (S+q) e := by
    simpa only [Nat.cast_add,Nat.cast_one,show S+((q:ℤ)+1)-1=S+q by omega] using hefil
  obtain ⟨e₂,error,herror,heiTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf 0 q hq S V ε hε e hefil'
  have hsum : f a₀-W' ≫ XModLambdaN.incl _ N=top+f e := by
    change f e=f (a₀-a) at hei
    have hei' : f e=f a₀-f a := by simpa only [f,positiveFiniteImage_sub] using hei
    rw [hei']
    dsimp only [top]
    abel
  have htop : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) (f a₀-W' ≫ XModLambdaN.incl _ N) =
      finiteMayTopLabel T.Y 0 q hq S (V+1) (v+error) := by
    rw [hsum,regrade_add,htopv,heiTop,finite_may_top_label_add]
  have ht := congrArg (homotopyRegrade
    (show ((V+1)-S)-1=((V+1)+q)-(S+q+1) by omega)
    (show (V+1)-(0:ℕ)=V+1 by omega)) htop
  refine ⟨e₂,error,herror,?_⟩
  simp only [a₀,f,ε,W',←positiveFiniteImage_regrade,←regrade_comp,source_top_regrade_sub,
    finiteMayTopLabel,last_layer_regrade_trans] at ht
  rw [top_label_at_weight_output_regrade] at ht
  simpa only [source_top_regrade_sub,top_target_regrade_self] using ht


private theorem early_positive_finite_source_top_at_degree
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N M : ℕ) (hq : 0 < q) (hN : N=0+(q+1)) (hNM : N≤M) (S V A B : ℤ)
    (hA : A=S+q+1) (hB : B=(V+1)+q)
    (u : Ambient background T.X (S,V))
    (v : Ambient background T.Y (A,B))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (ζ : BiHom (V-S) V
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) M))
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 M (by omega) = nativeFirstLabel T.X S V u)
    (cA : BiHom (V-S) V
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hcA : cA ≫ (background.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X S V u)
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V cA =
      W ≫ XModLambdaN.incl _ N +
        homotopyRegrade (show B-A=V-S by omega) rfl
          (finiteTopLabelAtWeight T.Y q hq N (by omega) A B (V+1) (by omega) v)) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (A,B),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=B-A by omega) rfl
        ((positiveFiniteImage T hf M (levelQuotientShiftIso T.X 1 M) (V-S) V ζ -
          W ≫ XModLambdaN.incl _ M) ≫ (background.quotients.tower _).rho N M hNM) =
        finiteTopLabelAtWeight T.Y q hq N (by omega) A B (V+1) (by omega) (v+error) := by
  subst N; subst A; subst B
  let aNative := ζ ≫ (background.quotients.tower _).rho (0+(q+1)) M hNM
  have hNative : aNative ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega)=
      nativeFirstLabel T.X S V u := by
    dsimp only [aNative]
    rw [Category.assoc,(background.quotients.tower _).rho_comp (by omega) hNM,hζ]
  let cA' := homotopyRegrade (rfl : V-S=V-S) (show V=V-(0:ℕ) by omega) cA
  have hcA' : cA' ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) =
      homotopyRegrade rfl (by omega) (nativeFirstLabel T.X S V u) := by
    dsimp only [cA']
    rw [←regrade_comp,hcA]
  have hcAi' : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega)
        (positiveFiniteImage T hf (0+(q+1)) (levelQuotientShiftIso T.X 1 (0+(q+1)))
          (V-S) (V-(0:ℕ)) cA') =
      homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show V+1=(V+1)-(0:ℕ) by omega) (W ≫ XModLambdaN.incl _ (0+(q+1))) +
        finiteMayTopLabel T.Y 0 q hq S (V+1) v := by
    dsimp only [cA']
    rw [←positiveFiniteImage_regrade,normalized_homotopy_regrade_trans,hcAi,regrade_add,
      normalized_homotopy_regrade_trans]
    unfold finiteMayTopLabel
    apply congrArg (fun z => homotopyRegrade
      (show V-S=((V+1)-S)-1 by omega) (show V+1=(V+1)-(0:ℕ) by omega)
      (W ≫ XModLambdaN.incl _ (0+(q+1))) + z)
    exact early_top_at_weight_congr T.Y q (0+q) (0+(q+1)) hq (by omega)
      (by omega) (by omega) (by omega) (S+q+1) ((V+1)+q) (V+1) ((V+1)-(0:ℕ))
      (((V+1)-S)-1) ((V+1)-(0:ℕ)) (by omega) (by omega) (by omega) (by omega) rfl v
  obtain ⟨e,error,he,ht⟩ := early_positive_same_finite_top T he hT hf hg hh q hq S V u v
    hmid aNative hNative cA' hcA' W hcAi'
  refine ⟨e,error,he,?_⟩
  rw [Preadditive.sub_comp,positive_finite_image_restriction T hf (0+(q+1)) M (by omega) hNM,
    Category.assoc,(background.quotients.tower _).rho_quotient]
  simpa only [aNative,Nat.zero_add] using ht

/-- Original early-boundary coordinates for the retained finite-source
comparison. The inputs are exactly the same compatible cA, u′, and W
produced from the displayed d₂ and d_L conditions. -/
private theorem early_positive_finite_source_top_at_early_level
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q N : ℕ) (hq : 2≤q) (hqN : q≤N) (s t : ℤ)
    (u : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hmid : ∀ j : ℕ, 1≤j → j<q-1 →
      ∀ a : Ambient background T.X ((s+1)+j,t+j),
        a ∈ cycles background T.X ((q:ℤ)-j) ((s+1)+j,t+j) →
        ∃ z : Ambient background T.Z ((s+1)+j,t+j+1),
          z ∈ cycles background T.Z ((q:ℤ)-j) ((s+1)+j,t+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+1)+j) (t+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+1)+j,t+j))
    (ζ : BiHom (t-(s+1)) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel T.X (s+1) t u)
    (cA : BiHom (t-(s+1)) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) ((q+1)-1)))
    (hcA : cA ≫ (background.quotients.tower _).rho 1 ((q+1)-1) (by omega)=
      nativeFirstLabel T.X (s+1) t u)
    (W : BiHom (t-(s+1)) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : positiveFiniteImage T hf ((q+1)-1) (levelQuotientShiftIso T.X 1 ((q+1)-1))
        (t-(s+1)) t cA = W ≫ XModLambdaN.incl _ ((q+1)-1) +
      homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega) rfl
        (finiteTopLabelAtWeight T.Y (q-1) (by omega) ((q+1)-1) (by omega)
          (s+q+1) (t+q) (t+1) (by omega) v)) :
    ∃ e : Ambient background T.X ((s+1)+(q-1),t+(q-1)),
    ∃ error : Ambient background T.Y (s+q+1,t+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+1)+(q-1)) (t+(q-1)) e) ∧
      homotopyRegrade (show t-(s+1)=(t+q)-(s+q+1) by omega) rfl
        ((positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-(s+1)) t ζ-
          W ≫ XModLambdaN.incl _ N) ≫ (background.quotients.tower _).rho ((q+1)-1) N (by omega)) =
        finiteTopLabelAtWeight T.Y (q-1) (by omega) ((q+1)-1) (by omega)
          (s+q+1) (t+q) (t+1) (by omega) (v+error) := by
  have hq' : q-1+1=q := by omega
  have H := early_positive_finite_source_top_at_degree T he hT hf hg hh (q-1) ((q+1)-1) N
    (by omega) (by omega) (by omega) (s+1) t (s+q+1) (t+q) (by omega) (by omega)
    u v (by simpa only [hq'] using hmid) ζ hζ cA hcA W hcAi
  obtain ⟨e,error,he,ht⟩ := H
  have transport (S V S' V' : ℤ) (hs : S=S') (hv : V=V')
      (a : Ambient background T.X (S,V)) :
      ∃ a' : Ambient background T.X (S',V'),
        HEq (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf S V a)
          (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf S' V' a') := by
    subst S'; subst V'
    exact ⟨a,HEq.rfl⟩
  obtain ⟨e',he'⟩ := transport _ _ ((s+1)+((q:ℤ)-1)) (t+((q:ℤ)-1))
    (by omega) (by omega) e
  exact ⟨e',error,he.trans he',ht⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
