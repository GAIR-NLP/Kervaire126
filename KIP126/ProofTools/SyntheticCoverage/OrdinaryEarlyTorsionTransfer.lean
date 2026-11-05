module

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyTransfer
import all KIP126.ProofTools.SyntheticCoverage.SelectiveBoundaryDifferential

/-! Finite-torsion early-boundary comparisons for the two ordinary
first-arrow branches. The corrected source determines both the error
and its torsion bound. -/

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

/-- The second-arrow branch moves the same finite residual to the last layer.
The specified full error supplies the torsion needed for each middle candidate. -/
private theorem torsion_ordinary_early_selective_top_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q l : ℕ) (hq : 0 < q) (hl : 0 < l) (B W : ℤ)
    (u : Ambient background T.X (B+1,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((l:ℤ)+j+1) ((B+1)+j-1+1,W+j) ≤ Pm j)
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
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) v))
    (ht : lambdaMultiply l (U ≫ background.nu.functor.map T.f-D)=0) :
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
  have H := torsion_selective_positive_g_native_residual_same_image T he hf hg hh hT
    0 (q+1) l (by omega) hl (B+1) W Pm
    (by simpa only [Nat.cast_zero,zero_add,add_assoc,add_comm,add_left_comm] using hPm) hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      lambdaMultiply l β=0 →
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
          ←XModLambdaN.incl_naturality]; abel) ht
  exact ordinary_early_full_source_top_of_residual T.X T.Y T.f q hq B W U D a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage

/-- The third-arrow branch retains the same finite image while eliminating
only the candidate directions allowed by the specified full-error torsion. -/
private theorem torsion_ordinary_early_selective_top_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q l : ℕ) (hq : 0 < q) (hl : 0 < l) (B W : ℤ)
    (u : Ambient background T.X (B+1,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((l:ℤ)+j+1) ((B+1)+j-1+1,W+j) ≤ Pm j)
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
        (show (W+q)-q=W by omega) (finiteTopLabel T.Y q hq (B+q+1) (W+q) v))
    (ht : lambdaMultiply l (U ≫ background.nu.functor.map T.f-D)=0) :
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
  have H := torsion_selective_positive_h_native_residual_same_image T he hf hg hh hT
    0 (q+1) l (by omega) hl (B+1) W Pm
    (by simpa only [Nat.cast_zero,zero_add,add_assoc,add_comm,add_left_comm] using hPm) hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      lambdaMultiply l β=0 →
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
          ←XModLambdaN.incl_naturality]; abel) ht
  exact ordinary_early_full_source_top_of_residual T.X T.Y T.f q hq B W U D a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage

/-- Torsion-sensitive ordinary target comparison with positive second arrow.
The corrected source itself supplies the torsion; the displayed source and
target and the complete terminal kernel are unchanged. -/
private theorem torsion_ordinary_early_target_of_compatible_source_second
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
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((N:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
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
  have ht : lambdaMultiply N
      (boundaryRepresentative T.X N s t ζ ≫ background.nu.functor.map T.f-W)=0 := by
    rw [←hξb]
    unfold boundaryRepresentative
    rw [lambda_regrade,absolute_boundary_lambda_zero,regrade_zero]
  obtain ⟨e,htop⟩ := torsion_ordinary_early_selective_top_second T he hT hf hg hh q N hq (by omega)
    (s+N) (t+N) u' v Pm hPm hmid (boundaryRepresentative T.X N s t ζ) hU a ha W hai ht
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

/-- Torsion-sensitive ordinary target comparison with positive third arrow.
The same corrected source supplies both the original first label and the
full boundary whose torsion controls the middle residual. -/
private theorem torsion_ordinary_early_target_of_compatible_source_third
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
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((N:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
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
  have ht : lambdaMultiply N
      (boundaryRepresentative T.X N s t ζ ≫ background.nu.functor.map T.f-W)=0 := by
    rw [←hξb]
    unfold boundaryRepresentative
    rw [lambda_regrade,absolute_boundary_lambda_zero,regrade_zero]
  obtain ⟨e,htop⟩ := torsion_ordinary_early_selective_top_third T he hT hf hg hh q N hq (by omega)
    (s+N) (t+N) u' v Pm hPm hmid (boundaryRepresentative T.X N s t ζ) hU a ha W hai ht
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

end
end KIP126.ProofTools.Internal.SyntheticCoverage
