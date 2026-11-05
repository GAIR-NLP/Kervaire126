module

import all KIP126.ProofTools.SyntheticCoverage.BottomFiniteLift

/-! Selective top comparison preserving the specified full source and early
absolute boundary. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem early_regrade_sub {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a b : BiHom m w A) :
    homotopyRegrade hm hw (a-b)=homotopyRegrade hm hw a-homotopyRegrade hm hw b := by
  subst m'; subst w'; rfl

private theorem early_top_at_weight_congr (X : (AdamsObject (coefficients := background.coefficients)))
    (d d' N : ℕ) (hd : 0<d) (hd' : 0<d') (hN : d+1=N) (hN' : d'+1=N)
    (he : d=d') (s t w w' m w0 : ℤ) (hw : t-d=w) (hw' : t-d'=w')
    (hm : t-s=m) (hw0 : w=w0) (hw0' : w'=w0) (x : Ambient background X (s,t)) :
    homotopyRegrade hm hw0 (finiteTopLabelAtWeight X d hd N hN s t w hw x)=
      homotopyRegrade hm hw0' (finiteTopLabelAtWeight X d' hd' N hN' s t w' hw' x) := by
  subst d'
  have hww : w=w' := hw.symm.trans hw'
  subst w'
  subst w0
  rfl

/-- Restricted middle elimination compares the same full source with the
specified early full boundary, retaining its literal last-layer error. -/
private theorem early_positive_selective_top
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
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      permanentCycles background T.Y (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u)
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
        ((verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf-W) ≫
          XModLambdaN.incl _ (0+(q+1))) =
        finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
          (S+q+1) ((V+1)+q) (V+1) (by omega) (v+error) := by
  let N := 0+(q+1)
  let ε := levelQuotientShiftIso T.X 1 N
  have hε := level_quotient_shift_incl T.X 1 N
  let a₀ : BiHom (V-S) (V-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    homotopyRegrade rfl (by omega) (U ≫ XModLambdaN.incl _ N)
  have hfirst : (U ≫ XModLambdaN.incl _ N) ≫
      (background.quotients.tower _).rho 1 N (by dsimp [N]; omega) =
      nativeFirstLabel T.X S V u := by
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X N (by dsimp [N]; omega)
    S V u _ hfirst
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
  let β := homotopyRegrade (rfl : V-S=V-S) (show V+1=(V-(0:ℕ))+1 by omega)
    (verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf-W)
  let top := f a-W' ≫ XModLambdaN.incl _ N
  have htopv : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) top =
      finiteMayTopLabel T.Y 0 q hq S (V+1) v := by
    dsimp only [top,f,a,ε,W']
    rw [early_regrade_sub,←regrade_comp,normalized_homotopy_regrade_trans,hcAi,add_sub_cancel_left]
  have hfull : f a₀-W' ≫ XModLambdaN.incl _ N = β ≫ XModLambdaN.incl _ N := by
    dsimp only [f,a₀,β,ε,W']
    rw [←positiveFiniteImage_regrade,positive_finite_image_full_projection,regrade_comp,
      early_regrade_sub,Preadditive.sub_comp,regrade_comp]
  have hvfil : FiltrationAtLeast background.syntheticTower (S+(q+1)) top := by
    apply (regrade_filtration_iff _ _ (S+(q+1)) top).mp
    rw [htopv]
    have hvd := finite_may_top_label_detects T.Y 0 q hq S (V+1) v
    have hvf := (regrade_filtration_iff _ _ (S+q+1) _).mp (detects_filtration
      (.quotient N (.nu T.Y)) (S+q+1,(V+1)+q,(V+1)-(0:ℕ)) _ _ hvd)
    simpa only [Nat.cast_add,Nat.cast_one,Int.add_assoc] using hvf
  obtain ⟨e,hefil,hei⟩ := selective_positive_f_native_residual_same_image
    T he hf hg hh hT 0 (q+1) (by omega) S V ε hε Pm hPm
    (by simpa only [Nat.cast_zero,zero_add] using hmid) (a₀-a) hres β top hvfil
    (by rw [positiveFiniteImage_sub,←hfull]; dsimp only [top]; abel)
  have hefil' : FiltrationAtLeast background.syntheticTower (S+q) e := by
    simpa only [Nat.cast_add,Nat.cast_one,show S+((q:ℤ)+1)-1=S+q by omega] using hefil
  obtain ⟨e₂,error,herror,heiTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf 0 q hq S V ε hε e hefil'
  have hsum : β ≫ XModLambdaN.incl _ N=top+f e := by
    change f e=f (a₀-a) at hei
    have hei' : f e=f a₀-f a := by simpa only [f,positiveFiniteImage_sub] using hei
    rw [←hfull,hei']
    dsimp only [top]
    abel
  have htop : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) (β ≫ XModLambdaN.incl _ N) =
      finiteMayTopLabel T.Y 0 q hq S (V+1) (v+error) := by
    rw [hsum,regrade_add,htopv,heiTop,finite_may_top_label_add]
  have ht := congrArg (homotopyRegrade
    (show ((V+1)-S)-1=((V+1)+q)-(S+q+1) by omega)
    (show (V+1)-(0:ℕ)=V+1 by omega)) htop
  refine ⟨e₂,error,herror,?_⟩
  simp only [β,←regrade_comp,finiteMayTopLabel,last_layer_regrade_trans] at ht
  rw [top_label_at_weight_output_regrade] at ht
  simpa only [top_target_regrade_self] using ht

private theorem early_positive_selective_top_at_degree
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hN : N=0+(q+1)) (S V A B : ℤ)
    (hA : A=S+q+1) (hB : B=(V+1)+q)
    (u : Ambient background T.X (S,V))
    (v : Ambient background T.Y (A,B))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      permanentCycles background T.Y (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u)
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
        ((verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf-W) ≫
          XModLambdaN.incl _ N) =
        finiteTopLabelAtWeight T.Y q hq N (by omega) A B (V+1) (by omega) (v+error) := by
  subst N; subst A; subst B
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
  obtain ⟨e,error,he,ht⟩ := early_positive_selective_top T he hT hf hg hh q hq S V u v
    Pm hPm hmid U hU cA' hcA' W hcAi'
  exact ⟨e,error,he,by simpa only [Nat.zero_add] using ht⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
