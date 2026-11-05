module

import all KIP126.ProofTools.SyntheticCoverage.EarlyTargetDifferential
import all KIP126.ProofTools.SyntheticCoverage.EarlySourceDifferential
import all KIP126.ProofTools.SyntheticCoverage.OrdinarySourceFinite
import all KIP126.ProofTools.SyntheticCoverage.SynchronizedBottomDifferential
import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyComparison

/-! Ordinary early-boundary comparisons with the specified common finite source. The actual common finite
source is an explicit hypothesis. -/

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

/-- Coefficient division of a specified ordinary finite source. The same
short source supplies both its first label and the actual early correction. -/
private theorem ordinary_early_top_division_and_torsion
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N i : ℕ) (hi : 0 < i) (hiN : i < N) (S V : ℤ)
    (u : Ambient background X (S,V))
    (a : BiHom (V-S) (V-i) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hsource : a≫(background.quotients.tower _).rho (i+1) N (by omega)=finiteTopLabel X i hi S V u)
    (v : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i)))
    (himage : a≫XModLambdaN.map (background.nu.functor.map f) N=
      finiteCoefficientShiftClass _ N i hiN (V-S) V v) :
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-i)),
    ∃ u' : Ambient background X (S,V),
    ∃ aHat : BiHom ((V-S)+1) (V-i) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) V (background.nu.functor.obj (Y.obj background.auxiliary)),
      finiteCoefficientShiftClass _ N i hiN (V-S) V b=a ∧
      b≫(background.quotients.tower _).rho 1 (N-i) (by omega)=nativeFirstLabel X S V u' ∧
      u'-u∈boundaries background X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega) (show (V-i)+i=V by omega)
        (biSuspensionHomEquiv ((V-S)+1) (V-i) i (background.nu.functor.obj (Y.obj background.auxiliary))
          (aHat≫XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      b≫XModLambdaN.map (background.nu.functor.map f) (N-i)=W≫XModLambdaN.incl _ (N-i)+v := by
  obtain ⟨b,u',hb,hu',hcong⟩ := early_native_top_division X N i hi hiN S V u a hsource
  let e := b≫XModLambdaN.map (background.nu.functor.map f) (N-i)-v
  have he : finiteCoefficientShiftClass _ N i hiN (V-S) V e=0 := by
    dsimp only [e]
    rw [early_coefficient_shift_sub,←finite_coefficient_shift_natural,hb,himage,sub_self]
  obtain ⟨aHat,W,hW,htors,heW⟩ := early_native_coefficient_kernel_at_weight Y i N hi hiN (V-S) V e he
  exact ⟨b,u',aHat,W,hb,hu',hcong,hW,htors,sub_eq_iff_eq_add.mp heW⟩

/-- Correct the image of one specified ordinary finite source by its
specified earlier boundary. This retains the first label and subtracts
exactly the same full correction, with all suspension comparisons kept. -/
private theorem ordinary_early_source_correction
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N i : ℕ) (hi : 0 < i) (hiN : i < N) (s t : ℤ)
    (x : Ambient background X (s,t))
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hζ : ζ≫(background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel X s t x)
    (aHat : BiHom (t-s) (t+N-i) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i)) :
    ∃ ξ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N),
      ξ≫(background.quotients.tower _).rho 1 N (by omega)=
        nativeFirstLabel Y s t ((background.classical.map f).pageMap 2 (s,t) x) ∧
      homotopyRegrade rfl (show t+N=(t+N-i)+i by omega)
        (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (Y.obj background.auxiliary))
          (ξ≫XModLambdaN.proj _ N))=
      homotopyRegrade rfl (show t+N=(t+N-i)+i by omega)
        (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (X.obj background.auxiliary))
          (ζ≫XModLambdaN.proj _ N))≫background.nu.functor.map f-
        biSuspensionHomEquiv (t-s) (t+N-i) i (background.nu.functor.obj (Y.obj background.auxiliary))
          (aHat≫XModLambdaN.proj _ i) := by
  obtain ⟨ξ,hξ,hb⟩ := finite_source_correction_of_earlier_boundary_at_weight Y (N-i) N i
    (by omega) (by omega) (by omega) (t-s) t (t+N-i) (by omega)
    (ζ≫XModLambdaN.map (background.nu.functor.map f) N) aHat
  refine ⟨ξ,?_,?_⟩
  · rw [hξ,Category.assoc,←(background.quotients.natural (background.nu.functor.map f)).rho_naturality,
      ←Category.assoc,hζ,native_first_label_natural]
  · rw [Category.assoc,XModLambdaN.proj_naturality,←Category.assoc,bi_susp_natural background.quotients.coherence] at hb
    simpa only [regrade_comp] using hb

/-- Corrected finite-image division with arbitrary short quotient length and
explicit classical degrees. The full correction has zero absolute boundary. -/
private theorem ordinary_early_source_differential_of_corrected_top
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d K N : ℕ) (hd : 0<d) (hK : K=d+1) (hKN : K≤N)
    (S V A B : ℤ) (hA : A=S+d) (hB : B=V+d)
    (u : Ambient background X (S+N+1,V+N))
    (y error : Ambient background Y (A,B))
    (ζ : BiHom (V-S) V
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hU : adjacentBoundaryLabel X N S V ζ = nativeFirstLabel X (S+N+1) (V+N) u)
    (W : BiHom (V-S) V (background.nu.functor.obj (Y.obj background.auxiliary)))
    (htop : homotopyRegrade (show V-S=B-A by omega) rfl
        ((ζ≫XModLambdaN.map (background.nu.functor.map f) N-
          W ≫ XModLambdaN.incl _ N) ≫ (background.quotients.tower _).rho K N hKN) =
      finiteTopLabelAtWeight Y d hd K (by omega) A B V (by omega) (y+error))
    (himage : error ∈ cycles background Y ((N-d:ℕ)+1) (A,B)) :
    let v := (background.classical.map f).pageMap 2 (S+N+1,V+N) u
    IsCycle background Y (N-d:ℕ) (A,B) y ∧
      IsCycle background Y (N-d:ℕ) (S+N+1,V+N) v ∧
      DifferentialAt background Y ((N-d:ℕ)+1) (A,B) (S+N+1,V+N) y v := by
  dsimp only
  let v := (background.classical.map f).pageMap 2 (S+N+1,V+N) u
  let v' : Ambient background Y (A+(N-d:ℕ)+1,B+(N-d:ℕ)) :=
    topClassicalRegrade (show (S+N+1,V+N)=(A+(N-d:ℕ)+1,B+(N-d:ℕ)) by
      ext <;> omega) v
  have hv' : HEq v' v := top_classical_regrade_heq _ _
  let η := ζ≫XModLambdaN.map (background.nu.functor.map f) N-
    W ≫ XModLambdaN.incl _ N
  let a : BiHom (B-A) V
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show V-S=B-A by omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho K N hKN =
      finiteTopLabelAtWeight Y d hd K (by omega) A B V (by omega) (y+error) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  have hb := ordinary_finite_image_boundary_label X Y f N S V u ζ hU
  dsimp only at hb
  rw [←finite_full_correction_boundary_unchanged _ N (V-S) V
    (ζ≫XModLambdaN.map (background.nu.functor.map f) N) W] at hb
  have hb' := congrArg (homotopyRegrade
    (show (V+N)-(S+N+1)=(B+(N-d:ℕ))-(A+(N-d:ℕ)+1) by omega)
    (show V+N=B+(N-d:ℕ) by omega)) hb
  rw [source_native_label_transport Y (S+N+1) (V+N)
    (A+(N-d:ℕ)+1) (B+(N-d:ℕ)) (by omega) (by omega) v v' hv'] at hb'
  have hba : homotopyRegrade (by omega) (by omega)
      (biSuspensionHomEquiv (B-A) V N (background.nu.functor.obj (Y.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel Y (A+(N-d:ℕ)+1) (B+(N-d:ℕ)) v' := by
    simpa only [a,η,source_boundary_regrade,regrade_comp,last_layer_regrade_trans] using hb'
  have hdiff := finite_source_differential_of_top_at_weight Y d N K hd (by omega) (by omega)
    A B V (by omega) (y+error) v' a ha hba
  have hdy := differential_of_source_later_cycle Y ((N-d:ℕ)+1)
    (A,B) (A+(N-d:ℕ)+1,B+(N-d:ℕ)) y (y+error) v' hdiff (by
      simpa only [sub_add_cancel_left,zero_sub] using
        (cycles background Y ((N-d:ℕ)+1) (A,B)).neg_mem himage)
  have hfinal := classical_differential_heq Y ((N-d:ℕ)+1) rfl
    (show (A+(N-d:ℕ)+1,B+(N-d:ℕ))=(S+N+1,V+N) by ext <;> omega)
    y y v' v HEq.rfl hv' hdy
  have hcycles := cycles_of_differential Y ((N-d:ℕ)+1) _ _ y v hfinal
  exact ⟨by simpa only [add_sub_cancel_right] using hcycles.1,
    by simpa only [add_sub_cancel_right] using hcycles.2,hfinal⟩

private theorem ordinary_early_full_source_top_of_residual
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (X.obj background.auxiliary)))
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (Y.obj background.auxiliary)))
    (a e : BiHom (W-(B+1)) W
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1)))
    (v : Ambient background Y (B+q+1,W+q))
    (hcommon : a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1) =
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel Y q hq (B+q+1) (W+q) v))
    (hefil : FiltrationAtLeast background.syntheticTower (B+q+1) e)
    (heimage : e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1) =
      (U ≫ XModLambdaN.incl _ (q+1)-a) ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)) :
    ∃ e₂ : Ambient background X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        ((U ≫ background.nu.functor.map f-D) ≫ XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (v+(background.classical.map f).pageMap 2 (B+q+1,W+q) e₂) := by
  let e' := homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl e
  have hefil' : FiltrationAtLeast background.syntheticTower (B+q+1) e' :=
    (regrade_filtration_iff _ _ _ _).mpr hefil
  obtain ⟨e₂,he₂⟩ := last_layer_ordinary_image_eq_top_at_weight X Y f q (q+1) hq rfl
    (B+q+1) (W+q) W (by omega) e' hefil'
  have hc := congrArg (homotopyRegrade
    (show W-(B+1)=(W+q)-(B+q+1) by omega) (rfl : W=W)) hcommon
  have hsum : (U ≫ background.nu.functor.map f-D) ≫ XModLambdaN.incl _ (q+1) =
      (a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1))+
        e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1) := by
    rw [heimage,Preadditive.sub_comp]
    rw [Preadditive.sub_comp,Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    abel
  refine ⟨e₂,?_⟩
  rw [hsum,regrade_add]
  have hc' : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      (a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega) v := by
    simpa only [finiteTopLabelAtWeight,last_layer_regrade_trans,top_target_regrade_self] using hc
  rw [hc']
  have he' : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      (e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        ((background.classical.map f).pageMap 2 (B+q+1,W+q) e₂) := by
    simpa only [e',←regrade_comp] using he₂
  rw [he',finite_top_label_at_weight_add]



/-- Ordinary restricted comparison, retaining the actual earlier correction. -/
private theorem ordinary_early_selective_top_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → permanentCycles background T.Y ((B+1)+j-1+1,W+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X ((B+1)+j-1+1,W+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j) →
        (background.classical.map T.f).pageMap 2 ((B+1)+j-1+1,W+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z ((B+1)+j-1+1,W+j+1),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j+1) ∧
        ∃ u : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            ((background.classical.map T.h).pageMap 2 ((B+1)+j-1+1,W+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((B+1)+j-1+1,W+j))
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u)
    (a : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (ha : a≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W u)
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hi : a≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) v)) :
    ∃ e₂ : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        ((U ≫ background.nu.functor.map T.f-D) ≫ XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (v+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂) := by
  let a₀ := U ≫ XModLambdaN.incl _ (q+1)
  have ha₀ : a₀ ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) =
      nativeFirstLabel T.X (B+1) W u := by
    dsimp only [a₀]
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a₀ ha₀
  have hdet' := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a ha
  have hres := detects_sub_filtration (background.convergence (.quotient (q+1) (.nu T.X)))
    (B+1,W,W) hdet hdet'
  have hvfil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)) := by
    rw [hi]
    apply (regrade_filtration_iff _ _ _ _).mpr
    exact detects_filtration (.quotient (q+1) (.nu T.Y)) (B+q+1,W+q,(W+q)-q) _ _
      (finiteTopLabel_detects T.Y q hq (B+q+1) (W+q) v)
  have H := selective_positive_g_native_residual_same_image T he hf hg hh hT
    0 (q+1) (by omega) (B+1) W Pm hPm hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      ∃ e : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
        FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) e ∧
        e ≫ XModLambdaN.map (background.nu.functor.map T.f) N =
          r ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
    subst N; subst w; exact H
  have H' := transport (q+1) W (by omega) (by omega)
  obtain ⟨e,hefil,heimage⟩ := H' (a₀-a) hres (U ≫ background.nu.functor.map T.f-D)
    (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1))
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by dsimp only [a₀]; simp only [Preadditive.sub_comp,Category.assoc,
          ←XModLambdaN.incl_naturality]; abel)
  exact ordinary_early_full_source_top_of_residual T.X T.Y T.f q hq B W U D a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage



/-- Ordinary restricted comparison, retaining the actual earlier correction. -/
private theorem ordinary_early_selective_top_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → permanentCycles background T.Y ((B+1)+j-1+1,W+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X ((B+1)+j-1+1,W+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j) →
        (background.classical.map T.f).pageMap 2 ((B+1)+j-1+1,W+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z ((B+1)+j-1,W+j),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((B+1)+j-1+1,W+j))
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u)
    (a : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (ha : a≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W u)
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hi : a≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) v)) :
    ∃ e₂ : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        ((U ≫ background.nu.functor.map T.f-D) ≫ XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (v+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂) := by
  let a₀ := U ≫ XModLambdaN.incl _ (q+1)
  have ha₀ : a₀ ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) =
      nativeFirstLabel T.X (B+1) W u := by
    dsimp only [a₀]
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a₀ ha₀
  have hdet' := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a ha
  have hres := detects_sub_filtration (background.convergence (.quotient (q+1) (.nu T.X)))
    (B+1,W,W) hdet hdet'
  have hvfil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)) := by
    rw [hi]
    apply (regrade_filtration_iff _ _ _ _).mpr
    exact detects_filtration (.quotient (q+1) (.nu T.Y)) (B+q+1,W+q,(W+q)-q) _ _
      (finiteTopLabel_detects T.Y q hq (B+q+1) (W+q) v)
  have H := selective_positive_h_native_residual_same_image T he hf hg hh hT
    0 (q+1) (by omega) (B+1) W Pm hPm hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      ∃ e : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
        FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) e ∧
        e ≫ XModLambdaN.map (background.nu.functor.map T.f) N =
          r ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
    subst N; subst w; exact H
  have H' := transport (q+1) W (by omega) (by omega)
  obtain ⟨e,hefil,heimage⟩ := H' (a₀-a) hres (U ≫ background.nu.functor.map T.f-D)
    (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1))
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by dsimp only [a₀]; simp only [Preadditive.sub_comp,Category.assoc,
          ←XModLambdaN.incl_naturality]; abel)
  exact ordinary_early_full_source_top_of_residual T.X T.Y T.f q hq B W U D a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage

/-- The original main differential and the genuinely early difference choose
one main source. Its ordinary image is corrected by exactly the produced W. -/
private theorem ordinary_early_corrected_source
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N i : ℕ) (hi : 0 < i) (hiN : i < N) (s t : ℤ)
    (x : Ambient background X (s,t)) (u u' : Ambient background X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (hu : u'-u∈boundaries background X (i+1) (s+N+1,t+N))
    (aHat : BiHom (((t+N)-(s+N+1))+1) ((t+N)-i)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i))
    (W : BiHom ((t+N)-(s+N+1)) (t+N) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hW : W=homotopyRegrade (show (((t+N)-(s+N+1))+1)-1=(t+N)-(s+N+1) by omega)
        (show ((t+N)-i)+i=t+N by omega)
        (biSuspensionHomEquiv (((t+N)-(s+N+1))+1) ((t+N)-i) i
          (background.nu.functor.obj (Y.obj background.auxiliary)) (aHat≫XModLambdaN.proj _ i))) :
    ∃ ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζ≫(background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel X s t x ∧
      adjacentBoundaryLabel X N s t ζ=nativeFirstLabel X (s+N+1) (t+N) u' ∧
      ∃ ξ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N),
        ξ≫(background.quotients.tower _).rho 1 N (by omega)=
          nativeFirstLabel Y s t ((background.classical.map f).pageMap 2 (s,t) x) ∧
        boundaryRepresentative Y N s t ξ=boundaryRepresentative X N s t ζ≫background.nu.functor.map f-W := by
  have hd' := differential_of_earlier_boundaries X (N+1) (i+1) (i+1)
    (s,t) (s+N+1,t+N) x x u u' ⟨by omega,hdx⟩ (by omega) (by omega)
    (by rw [sub_self]; exact (boundaries background X (i+1) (s,t)).zero_mem) hu
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift X N (by omega) s t x u').mp hd'.2
  let a₀ := homotopyRegrade (show ((t+N)-(s+N+1))+1=t-s by omega) rfl aHat
  obtain ⟨ξ,hξ,hb⟩ := ordinary_early_source_correction X Y f N i hi hiN s t x ζ hζ a₀
  refine ⟨ζ,hζ,hU,ξ,hξ,?_⟩
  have hb' := congrArg (homotopyRegrade
    (show (t-s)-1=(t+N)-(s+N+1) by omega) (show ((t+N)-i)+i=t+N by omega)) hb
  have hWa : homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega)
      (show ((t+N)-i)+i=t+N by omega)
      (biSuspensionHomEquiv (t-s) (t+N-i) i (background.nu.functor.obj (Y.obj background.auxiliary))
        (a₀≫XModLambdaN.proj _ i))=W := by
    simpa only [a₀,←regrade_comp,early_bi_susp_regrade,normalized_homotopy_regrade_trans] using hW.symm
  rw [homotopy_regrade_sub,hWa] at hb'
  simpa only [boundaryRepresentative,regrade_comp,normalized_homotopy_regrade_trans] using hb'

/-- Conditional final target comparison for the ordinary second branch.
The common finite source and its actual early boundary are explicit inputs;
the original middle spaces, whole terminal kernel, and displayed y are kept. -/
private theorem ordinary_early_target_of_compatible_source_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (N i q : ℕ) (hi : 0 < i) (hiN : i < N) (hq : 0 < q) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (y : Ambient background T.Y (s,t))
    (hy : y-(background.classical.map T.f).pageMap 2 (s,t) x∈boundaries background T.Y N (s,t))
    (u u' : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (hu : u'-u∈boundaries background T.X (i+1) (s+N+1,t+N))
    (v : Ambient background T.Y ((s+N)+q+1,(t+N)+q))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → permanentCycles background T.Y (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z (((s+N)+1)+j-1+1,(t+N)+j+1),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j+1) ∧
        ∃ u : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
          (background.classicalSuspension T.X).DesuspendsClass (((s+N)+1)+j-1+1) ((t+N)+j+1)
            ((background.classical.map T.h).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j))
    (a : BiHom ((t+N)-(s+N+1)) (t+N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (ha : a≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (s+N+1) (t+N) u')
    (aHat : BiHom (((t+N)-(s+N+1))+1) ((t+N)-i)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i))
    (W : BiHom ((t+N)-(s+N+1)) (t+N) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hW : W=homotopyRegrade (show (((t+N)-(s+N+1))+1)-1=(t+N)-(s+N+1) by omega)
        (show ((t+N)-i)+i=t+N by omega)
        (biSuspensionHomEquiv (((t+N)-(s+N+1))+1) ((t+N)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat≫XModLambdaN.proj _ i)))
    (hai : a≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-W≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show ((t+N)+q)-((s+N)+q+1)=(t+N)-(s+N+1) by omega)
        (show ((t+N)+q)-q=t+N by omega) (finiteTopLabel T.Y q hq ((s+N)+q+1) ((t+N)+q) v))
    (P : Submodule ℤ (Ambient background T.Y ((s+N)+q+1,(t+N)+q)))
    (hP : permanentCycles background T.Y ((s+N)+q+1,(t+N)+q)≤P) (hv : v∈P)
    (hker : ∀ z∈P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+N)+q+1) ((t+N)+q) z=0 →
      z∈boundaries background T.Y (N+q:ℕ) ((s+N)+q+1,(t+N)+q)) :
    IsCycle background T.Y (N+q:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+q:ℕ) ((s+N)+q+1,(t+N)+q) v ∧
      DifferentialAt background T.Y ((N+q:ℕ)+1) (s,t) ((s+N)+q+1,(t+N)+q) y v := by
  obtain ⟨ζ,hζ,hU,ξ,hξ,hξb⟩ := ordinary_early_corrected_source T.X T.Y T.f
    N i hi hiN s t x u u' hdx hu aHat W hW
  obtain ⟨e,htop⟩ := ordinary_early_selective_top_second T he hT hf hg hh q hq
    (s+N) (t+N) u' v Pm hPm hmid (boundaryRepresentative T.X N s t ζ) hU a ha W hai
  let error := (background.classical.map T.f).pageMap 2 ((s+N)+q+1,(t+N)+q) e
  have htop' : homotopyRegrade (show (t-s)-1=((t+N)+q)-((s+N)+q+1) by omega)
      (show t+N=((t+N)+q)-q by omega)
      (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (ξ≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ (q+1))=
      finiteTopLabel T.Y q hq ((s+N)+q+1) ((t+N)+q) (v+error) := by
    rw [←hξb] at htop
    have h := congrArg (homotopyRegrade
      (rfl : ((t+N)+q)-((s+N)+q+1)=((t+N)+q)-((s+N)+q+1))
      (show t+N=((t+N)+q)-q by omega)) htop
    simpa only [boundaryRepresentative,←regrade_comp,normalized_homotopy_regrade_trans,
      finiteTopLabelAtWeight,top_target_regrade_self] using h
  have hd := synchronized_first_differential_at_degree T.Y N q (by omega) hq s t
    ((s+N)+q+1) ((t+N)+q) (by omega) (by omega)
    ((background.classical.map T.f).pageMap 2 (s,t) x) ξ hξ v error P hP hv
    (fun heP => hker error heP (positive_second_triangle_composite_zero T hf hg hh hT ((s+N)+q+1) ((t+N)+q) e)) htop'
  simpa only [add_sub_cancel_right] using early_target_of_page_source T.Y ((N+q:ℕ)+1) N
    (s,t) ((s+N)+q+1,(t+N)+q) (by omega) _ y v hd.2.2 hy


/-- Conditional final target comparison for the ordinary third branch.
The common finite source and its actual early boundary are explicit inputs;
the original middle spaces, whole terminal kernel, and displayed y are kept. -/
private theorem ordinary_early_target_of_compatible_source_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (N i q : ℕ) (hi : 0 < i) (hiN : i < N) (hq : 0 < q) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (y : Ambient background T.Y (s,t))
    (hy : y-(background.classical.map T.f).pageMap 2 (s,t) x∈boundaries background T.Y N (s,t))
    (u u' : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (hu : u'-u∈boundaries background T.X (i+1) (s+N+1,t+N))
    (v : Ambient background T.Y ((s+N)+q+1,(t+N)+q))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → permanentCycles background T.Y (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z (((s+N)+1)+j-1,(t+N)+j),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) (((s+N)+1)+j-1,(t+N)+j) ∧
        ∃ u : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
          (background.classicalSuspension T.X).DesuspendsClass (((s+N)+1)+j-1+1) ((t+N)+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (((s+N)+1)+j-1) ((t+N)+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j))
    (a : BiHom ((t+N)-(s+N+1)) (t+N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (ha : a≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (s+N+1) (t+N) u')
    (aHat : BiHom (((t+N)-(s+N+1))+1) ((t+N)-i)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i))
    (W : BiHom ((t+N)-(s+N+1)) (t+N) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hW : W=homotopyRegrade (show (((t+N)-(s+N+1))+1)-1=(t+N)-(s+N+1) by omega)
        (show ((t+N)-i)+i=t+N by omega)
        (biSuspensionHomEquiv (((t+N)-(s+N+1))+1) ((t+N)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat≫XModLambdaN.proj _ i)))
    (hai : a≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-W≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show ((t+N)+q)-((s+N)+q+1)=(t+N)-(s+N+1) by omega)
        (show ((t+N)+q)-q=t+N by omega) (finiteTopLabel T.Y q hq ((s+N)+q+1) ((t+N)+q) v))
    (P : Submodule ℤ (Ambient background T.Y ((s+N)+q+1,(t+N)+q)))
    (hP : permanentCycles background T.Y ((s+N)+q+1,(t+N)+q)≤P) (hv : v∈P)
    (hker : ∀ z∈P, (background.classical.map T.g).pageMap 2 ((s+N)+q+1,(t+N)+q) z=0 →
      z∈boundaries background T.Y (N+q:ℕ) ((s+N)+q+1,(t+N)+q)) :
    IsCycle background T.Y (N+q:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+q:ℕ) ((s+N)+q+1,(t+N)+q) v ∧
      DifferentialAt background T.Y ((N+q:ℕ)+1) (s,t) ((s+N)+q+1,(t+N)+q) y v := by
  obtain ⟨ζ,hζ,hU,ξ,hξ,hξb⟩ := ordinary_early_corrected_source T.X T.Y T.f
    N i hi hiN s t x u u' hdx hu aHat W hW
  obtain ⟨e,htop⟩ := ordinary_early_selective_top_third T he hT hf hg hh q hq
    (s+N) (t+N) u' v Pm hPm hmid (boundaryRepresentative T.X N s t ζ) hU a ha W hai
  let error := (background.classical.map T.f).pageMap 2 ((s+N)+q+1,(t+N)+q) e
  have htop' : homotopyRegrade (show (t-s)-1=((t+N)+q)-((s+N)+q+1) by omega)
      (show t+N=((t+N)+q)-q by omega)
      (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (ξ≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ (q+1))=
      finiteTopLabel T.Y q hq ((s+N)+q+1) ((t+N)+q) (v+error) := by
    rw [←hξb] at htop
    have h := congrArg (homotopyRegrade
      (rfl : ((t+N)+q)-((s+N)+q+1)=((t+N)+q)-((s+N)+q+1))
      (show t+N=((t+N)+q)-q by omega)) htop
    simpa only [boundaryRepresentative,←regrade_comp,normalized_homotopy_regrade_trans,
      finiteTopLabelAtWeight,top_target_regrade_self] using h
  have hd := synchronized_first_differential_at_degree T.Y N q (by omega) hq s t
    ((s+N)+q+1) ((t+N)+q) (by omega) (by omega)
    ((background.classical.map T.f).pageMap 2 (s,t) x) ξ hξ v error P hP hv
    (fun heP => hker error heP (ordinary_triangle_composite_zero T ((s+N)+q+1) ((t+N)+q) e)) htop'
  simpa only [add_sub_cancel_right] using early_target_of_page_source T.Y ((N+q:ℕ)+1) N
    (s,t) ((s+N)+q+1,(t+N)+q) (by omega) _ y v hd.2.2 hy

/-- Whole-middle elimination on the same native ordinary residual. -/
private theorem ordinary_early_native_whole_middle_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c q : ℕ) (hq : 0 < q) (B W : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (a : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (ha : FiltrationAtLeast background.syntheticTower ((B+1)+1) a) :
    ∃ e : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))),
      FiltrationAtLeast background.syntheticTower (B+q+1) e ∧
      e≫XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1))=
        a≫XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1)) := by
  let N := c+(q+1)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨raw,hraw⟩ := ordinary_source_desuspend_surjective T he hf N c B W ε a
  have hrawfil : FiltrationAtLeast background.syntheticTower ((B+1)+1)
      (positiveHSourceDesuspend T he hf N c B W ε raw) := by rw [hraw]; exact ha
  obtain ⟨e,hefil,hei⟩ := positive_second_last_residual T he hf hg hh hT c q hq B W hmid ε raw hrawfil
  refine ⟨positiveHSourceDesuspend T he hf N c B W ε e,hefil,?_⟩
  have hz := middle_raw_ordinary_image_zero_implies_native_zero T he hf N c (by dsimp [N];omega)
    B W ε hε (e-raw) (by rw [Preadditive.sub_comp,hei,sub_self])
  rw [positive_h_source_desuspend_sub,Preadditive.sub_comp,hraw] at hz
  exact sub_eq_zero.mp hz


/-- Whole-middle elimination on the same native ordinary residual. -/
private theorem ordinary_early_native_whole_middle_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (c q : ℕ) (hq : 0 < q) (B W : ℤ)
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
    (a : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (ha : FiltrationAtLeast background.syntheticTower ((B+1)+1) a) :
    ∃ e : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))),
      FiltrationAtLeast background.syntheticTower (B+q+1) e ∧
      e≫XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1))=
        a≫XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1)) := by
  let N := c+(q+1)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨raw,hraw⟩ := ordinary_source_desuspend_surjective T he hf N c B W ε a
  have hrawfil : FiltrationAtLeast background.syntheticTower ((B+1)+1)
      (positiveHSourceDesuspend T he hf N c B W ε raw) := by rw [hraw]; exact ha
  have hres := middle_positive_h_residual_same_image T he hf hg hh hT c (q+1) (by omega) (B+1) W
    (fun j hj hjq b hb => by
      obtain ⟨z,hz,u,hu,hbu⟩ := hmid j hj hjq b hb
      exact ⟨z,hz,u,hu,boundaries_monotone background T.X _ (by omega) hbu⟩) ε
  rw [show B+1-1=B by omega] at hres
  obtain ⟨e,hefil',hei⟩ := hres raw hrawfil
  have hefil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (positiveHSourceDesuspend T he hf N c B W ε e) := by
    simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil'
  refine ⟨positiveHSourceDesuspend T he hf N c B W ε e,hefil,?_⟩
  have hz := middle_raw_ordinary_image_zero_implies_native_zero T he hf N c (by dsimp [N];omega)
    B W ε hε (e-raw) (by rw [Preadditive.sub_comp,hei,sub_self])
  rw [positive_h_source_desuspend_sub,Preadditive.sub_comp,hraw] at hz
  exact sub_eq_zero.mp hz

private theorem ordinary_early_finite_source_top_of_residual
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (aNative : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1)))
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (Y.obj background.auxiliary)))
    (a e : BiHom (W-(B+1)) W
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1)))
    (v : Ambient background Y (B+q+1,W+q))
    (hcommon : a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1) =
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel Y q hq (B+q+1) (W+q) v))
    (hefil : FiltrationAtLeast background.syntheticTower (B+q+1) e)
    (heimage : e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1) =
      (aNative-a) ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)) :
    ∃ e₂ : Ambient background X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        (aNative≫XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (v+(background.classical.map f).pageMap 2 (B+q+1,W+q) e₂) := by
  let e' := homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl e
  have hefil' : FiltrationAtLeast background.syntheticTower (B+q+1) e' :=
    (regrade_filtration_iff _ _ _ _).mpr hefil
  obtain ⟨e₂,he₂⟩ := last_layer_ordinary_image_eq_top_at_weight X Y f q (q+1) hq rfl
    (B+q+1) (W+q) W (by omega) e' hefil'
  have hc := congrArg (homotopyRegrade
    (show W-(B+1)=(W+q)-(B+q+1) by omega) (rfl : W=W)) hcommon
  have hsum : aNative≫XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1) =
      (a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1))+
        e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1) := by
    rw [heimage,Preadditive.sub_comp]
    abel
  refine ⟨e₂,?_⟩
  rw [hsum,regrade_add]
  have hc' : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      (a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)-D≫XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega) v := by
    simpa only [finiteTopLabelAtWeight,last_layer_regrade_trans,top_target_regrade_self] using hc
  rw [hc']
  have he' : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      (e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        ((background.classical.map f).pageMap 2 (B+q+1,W+q) e₂) := by
    simpa only [e',←regrade_comp] using he₂
  rw [he',finite_top_label_at_weight_add]




/-- Whole-M comparison retains the specified finite main source and W. -/
private theorem ordinary_early_same_finite_top_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (y : Ambient background T.Y (B+q+1,W+q))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (aNative cA : BiHom (W-(B+1)) W
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (hNative : aNative≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W u)
    (hcA : cA≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W u)
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hi : cA≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) y)) :
    ∃ e : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        (aNative≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1))=
        finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
          (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) := by
  have hres := detects_sub_filtration (background.convergence (.quotient (q+1) (.nu T.X))) (B+1,W,W)
    (first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u aNative hNative)
    (first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u cA hcA)
  have H := ordinary_early_native_whole_middle_second T he hf hg hh hT 0 q hq B W hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ a : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) a →
      ∃ e : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
        FiltrationAtLeast background.syntheticTower (B+q+1) e ∧
        e≫XModLambdaN.map (background.nu.functor.map T.f) N=a≫XModLambdaN.map (background.nu.functor.map T.f) N := by
    subst N; subst w; exact H
  obtain ⟨e,hefil,hei⟩ := transport (q+1) W (by omega) (by omega) (aNative-cA) hres
  exact ordinary_early_finite_source_top_of_residual T.X T.Y T.f q hq B W aNative D cA e y hi hefil hei


/-- Whole-M comparison retains the specified finite main source and W. -/
private theorem ordinary_early_same_finite_top_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (y : Ambient background T.Y (B+q+1,W+q))
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
    (aNative cA : BiHom (W-(B+1)) W
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (hNative : aNative≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W u)
    (hcA : cA≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W u)
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hi : cA≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) y)) :
    ∃ e : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        (aNative≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1))=
        finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
          (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) := by
  have hres := detects_sub_filtration (background.convergence (.quotient (q+1) (.nu T.X))) (B+1,W,W)
    (first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u aNative hNative)
    (first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u cA hcA)
  have H := ordinary_early_native_whole_middle_third T he hf hg hh hT 0 q hq B W hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ a : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) a →
      ∃ e : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
        FiltrationAtLeast background.syntheticTower (B+q+1) e ∧
        e≫XModLambdaN.map (background.nu.functor.map T.f) N=a≫XModLambdaN.map (background.nu.functor.map T.f) N := by
    subst N; subst w; exact H
  obtain ⟨e,hefil,hei⟩ := transport (q+1) W (by omega) (by omega) (aNative-cA) hres
  exact ordinary_early_finite_source_top_of_residual T.X T.Y T.f q hq B W aNative D cA e y hi hefil hei

/-- Source-side comparison under complete-image survival. The early
source boundary has arbitrary cutoff, with the bound `q+1≤N`. -/
private theorem ordinary_early_source_of_compatible_source_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1≤N) (B W b : ℤ)
    (x x' : Ambient background T.X (B+1,W)) (u : Ambient background T.X ((B+1)+N+1,W+N))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (hxx : x'-x∈boundaries background T.X b (B+1,W))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (cA : BiHom (W-(B+1)) W
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (hcA : cA≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W x')
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hi : cA≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) y))
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e∈cycles background T.Y ((N-q:ℕ)+1) (B+q+1,W+q)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-q:ℕ) (B+q+1,W+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (B+q+1,W+q) ((B+1)+N+1,W+N) y v := by
  have hdx' := differential_of_source_boundary_congruent T.X (N+1) b
    (B+1,W) ((B+1)+N+1,W+N) x' x u hdx hxx
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega) (B+1) W x' u).mp hdx'
  let aNative := ζ≫(background.quotients.tower _).rho (q+1) N hqN
  have hNative : aNative≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W x' := by
    dsimp only [aNative]
    rw [Category.assoc,(background.quotients.tower _).rho_comp,hζ]
  obtain ⟨e,htop⟩ := ordinary_early_same_finite_top_second T he hT hf hg hh q hq B W
    x' y hmid aNative cA hNative hcA D hi
  have hlong : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) N-D≫XModLambdaN.incl _ N)≫
        (background.quotients.tower _).rho (q+1) N hqN)=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) := by
    rw [Preadditive.sub_comp,Category.assoc,
      ←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality hqN,
      ←Category.assoc,Category.assoc D,(background.quotients.tower _).rho_quotient]
    exact htop
  exact ordinary_early_source_differential_of_corrected_top T.X T.Y T.f q (q+1) N hq rfl hqN
    (B+1) W (B+q+1) (W+q) (by omega) rfl u y _ ζ hU D hlong (himage e)


/-- Source-side comparison under complete-image survival. The early
source boundary has arbitrary cutoff, with the bound `q+1≤N`. -/
private theorem ordinary_early_source_of_compatible_source_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1≤N) (B W b : ℤ)
    (x x' : Ambient background T.X (B+1,W)) (u : Ambient background T.X ((B+1)+N+1,W+N))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (hxx : x'-x∈boundaries background T.X b (B+1,W))
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
    (cA : BiHom (W-(B+1)) W
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (hcA : cA≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W x')
    (D : BiHom (W-(B+1)) W (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hi : cA≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)-D≫XModLambdaN.incl _ (q+1)=
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) y))
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e∈cycles background T.Y ((N-q:ℕ)+1) (B+q+1,W+q)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-q:ℕ) (B+q+1,W+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (B+q+1,W+q) ((B+1)+N+1,W+N) y v := by
  have hdx' := differential_of_source_boundary_congruent T.X (N+1) b
    (B+1,W) ((B+1)+N+1,W+N) x' x u hdx hxx
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega) (B+1) W x' u).mp hdx'
  let aNative := ζ≫(background.quotients.tower _).rho (q+1) N hqN
  have hNative : aNative≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X (B+1) W x' := by
    dsimp only [aNative]
    rw [Category.assoc,(background.quotients.tower _).rho_comp,hζ]
  obtain ⟨e,htop⟩ := ordinary_early_same_finite_top_third T he hT hf hg hh q hq B W
    x' y hmid aNative cA hNative hcA D hi
  have hlong : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) N-D≫XModLambdaN.incl _ N)≫
        (background.quotients.tower _).rho (q+1) N hqN)=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) := by
    rw [Preadditive.sub_comp,Category.assoc,
      ←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality hqN,
      ←Category.assoc,Category.assoc D,(background.quotients.tower _).rho_quotient]
    exact htop
  exact ordinary_early_source_differential_of_corrected_top T.X T.Y T.f q (q+1) N hq rfl hqN
    (B+1) W (B+q+1) (W+q) (by omega) rfl u y _ ζ hU D hlong (himage e)


end
end KIP126.ProofTools.Internal.SyntheticCoverage
