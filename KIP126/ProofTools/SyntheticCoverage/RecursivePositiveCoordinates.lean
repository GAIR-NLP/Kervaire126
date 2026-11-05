module

import all KIP126.ProofTools.SyntheticCoverage.RecursiveDifferential

/-! Fixed positive-boundary coordinates for the recursive finite relation.
The selected sphere automorphism is conjugated into the recursive source
coordinates and retained on full homotopy groups. -/

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

private def recursiveSphereRegradeIso {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w) :
    Smn (Syn:=SyntheticSpectrum) m' w' ≅ Smn m' w' := by
  subst m'; subst w'; exact u

private theorem recursive_sphere_regrade_precomp {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w) (a : BiHom m w A) :
    (recursiveSphereRegradeIso hm hw u).hom ≫ homotopyRegrade hm hw a=
      homotopyRegrade hm hw (u.hom ≫ a) := by
  subst m'; subst w'; rfl

/-- This single fixed automorphism is used before and after every
synchronized correction of the finite source. -/
private def recursivePositiveBoundaryIso (N : ℕ) (s t : ℤ) :
    Smn (Syn:=SyntheticSpectrum) (t-s) (t-1) ≅ Smn (t-s) (t-1) :=
  recursiveSphereRegradeIso (show (t-s+1)-1=t-s by omega)
    (show (t-1-N)+N=t-1 by omega) (positiveBoundarySourceIso 1 N (t-s+1) (t-1-N))

private theorem recursive_positive_boundary_coordinate
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (s t : ℤ)
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    (recursivePositiveBoundaryIso N s t).hom ≫ recursiveBoundaryRepresentative X N s t ζ=
      homotopyRegrade (show (t-s+1)-1=t-s by omega) (show (t-1-N)+N=t-1 by omega)
        ((positiveBoundarySourceIso 1 N (t-s+1) (t-1-N)).hom ≫
          biSuspensionHomEquiv (t-s+1) (t-1-N) N
            (background.nu.functor.obj (X.obj background.auxiliary)) (ζ ≫ XModLambdaN.proj _ N)) := by
  exact recursive_sphere_regrade_precomp _ _ _ _

private theorem recursive_positive_boundary_first
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (s t : ℤ)
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    ((recursivePositiveBoundaryIso N s t).hom ≫ recursiveBoundaryRepresentative X N s t ζ) ≫
      XModLambdaN.incl _ 1=recursiveBoundaryRepresentative X N s t ζ ≫ XModLambdaN.incl _ 1 := by
  rw [Category.assoc,sphere_automorphism_quotient_projection]

/-- Exact naturality of the actual positive finite image boundary. The
fixed source automorphism remains present on the full source group. -/
private theorem recursive_positive_absolute_boundary_coordinates
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (m w : ℤ)
    (ζ : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    verticalTranslate _ 1 (m-1) (w+N)
        ((positiveBoundarySourceIso 1 N m w).hom ≫
          biSuspensionHomEquiv m w N (background.nu.functor.obj (T.X.obj background.auxiliary))
            (ζ ≫ XModLambdaN.proj _ N)) ≫ lastLayerNormalizedMap T hf=
      homotopyRegrade rfl (show (w+1)+N=(w+N)+1 by omega)
        (biSuspensionHomEquiv m (w+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w ζ ≫
            XModLambdaN.proj _ N)) := by
  rw [shifted_absolute_boundary_eq_precomp,←regrade_comp,recursive_positive_image_as_translate]
  simp only [Category.assoc]
  rw [XModLambdaN.proj_naturality]
  simp only [←Category.assoc]
  rw [bi_susp_natural background.quotients.coherence]
  rfl

private theorem recursive_positive_full_boundary_square
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (s t : ℤ)
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    verticalTranslate _ 1 (t-s) (t-1)
        ((recursivePositiveBoundaryIso N s t).hom ≫ recursiveBoundaryRepresentative T.X N s t ζ) ≫
          lastLayerNormalizedMap T hf=
      homotopyRegrade (show (t-s+1)-1=t-s by omega) (show ((t-1-N)+1)+N=(t-1)+1 by omega)
        (biSuspensionHomEquiv (t-s+1) ((t-1-N)+1) N
          (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ ≫
            XModLambdaN.proj _ N)) := by
  rw [recursive_positive_boundary_coordinate,vertical_translate_regrade,←regrade_comp,
    recursive_positive_absolute_boundary_coordinates,normalized_homotopy_regrade_trans]

private theorem recursive_positive_boundary_square
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (s t : ℤ)
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    recursivePositiveImage T hf s t
        (((recursivePositiveBoundaryIso N s t).hom ≫ recursiveBoundaryRepresentative T.X N s t ζ) ≫
          XModLambdaN.incl _ 3)=
      homotopyRegrade (show (t-s+1)-1=t-s by omega) (show ((t-1-N)+1)+N=t by omega)
        (biSuspensionHomEquiv (t-s+1) ((t-1-N)+1) N
          (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ ≫
            XModLambdaN.proj _ N) ≫ XModLambdaN.incl _ 3) := by
  simp only [recursivePositiveImage,positive_finite_image_full_projection]
  rw [recursive_positive_full_boundary_square,←regrade_comp,normalized_homotopy_regrade_trans]

private theorem recursive_positive_top_filtration (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (v : Ambient background X (s+1+1,(t+1)+1)) :
    FiltrationAtLeast background.syntheticTower (s+2) (recursivePositiveTopLabel X s t v) := by
  apply (regrade_filtration_iff _ _ _ _).mpr
  have h : FiltrationAtLeast background.syntheticTower (s+1+1)
      (finiteTopLabel X 2 (by decide) (s+1+1) ((t+1)+1) v) :=
    KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 3 (.nu X))
      (s+1+1,(t+1)+1,((t+1)+1)-2) _ _
      (finiteTopLabel_detects X 2 (by decide) (s+1+1) ((t+1)+1) v)
  simpa only [show s+1+1=s+2 by omega] using h

/-- The top candidate is above the actual error head, so the head's
positive image is detected by the image of the same full representative. -/
private theorem recursive_positive_error_image_detects
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ)
    (a : BiHom (t-s) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v)
    (x : Ambient background T.X (s,t))
    (hx : Detects (background.convergence (.quotient 3 (.nu T.X))) (s,t,t-1)
      (finiteTargetLabel background T.X 3 s t 1 x) (a≫XModLambdaN.incl _ 3-c)) :
    Detects (background.convergence (.quotient 3 (.nu T.Y))) (s+1,t+1,(t+1)-1)
      (finiteTargetLabel background T.Y 3 (s+1) (t+1) 1
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x))
      (homotopyRegrade (show t-s=(t+1)-(s+1) by omega) (show t=(t+1)-1 by omega)
        (recursivePositiveImage T hf s t (a≫XModLambdaN.incl _ 3))) := by
  have hmap := selective_positive_image_detects T hf 3 1 (by decide) (by decide)
    s t (levelQuotientShiftIso T.X 1 3) (level_quotient_shift_incl T.X 1 3) x _ hx
  have hmap' : Detects (background.convergence (.quotient 3 (.nu T.Y))) (s+1,t+1,(t+1)-1)
      (finiteTargetLabel background T.Y 3 (s+1) (t+1) 1
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x))
      (homotopyRegrade (show t-s=(t+1)-(s+1) by omega) (show t=(t+1)-1 by omega)
        (recursivePositiveImage T hf s t (a≫XModLambdaN.incl _ 3-c))) := by
    convert hmap using 1 <;>
      simp only [recursivePositiveImage,normalized_homotopy_regrade_trans,Nat.cast_one]
    all_goals rfl
  apply detects_of_next_filtration_difference (.quotient 3 (.nu T.Y)) (s+1,t+1,(t+1)-1)
    _ _ _ hmap'
  rw [←homotopy_regrade_sub,recursive_positive_image_sub,sub_sub_cancel,hc]
  apply (regrade_filtration_iff _ _ _ _).mpr
  simpa only [show (s+1)+1=s+2 by omega] using recursive_positive_top_filtration T.Y s t v

private theorem recursive_positive_boundary_error_detects
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (s t : ℤ)
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v)
    (x : Ambient background T.X (s,t))
    (hx : Detects (background.convergence (.quotient 3 (.nu T.X))) (s,t,t-1)
      (finiteTargetLabel background T.X 3 s t 1 x)
      (((recursivePositiveBoundaryIso N s t).hom≫recursiveBoundaryRepresentative T.X N s t ζ)≫
        XModLambdaN.incl _ 3-c)) :
    Detects (background.convergence (.quotient 3 (.nu T.Y))) (s+1,t+1,(t+1)-1)
      (finiteTargetLabel background T.Y 3 (s+1) (t+1) 1
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x))
      (homotopyRegrade (show (t-s+1)-1=(t+1)-(s+1) by omega)
        (show ((t-1-N)+1)+N=(t+1)-1 by omega)
        (biSuspensionHomEquiv (t-s+1) ((t-1-N)+1) N
          (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ≫
            XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)) := by
  have h := recursive_positive_error_image_detects T hf s t _ c v hc x hx
  rw [recursive_positive_boundary_square,normalized_homotopy_regrade_trans] at h
  exact h

/-- The K1=1 positive head gate uses the actual image of the same original
finite source. Its canonical absolute boundary is identified by the fixed
coordinate square above. -/
private theorem recursive_positive_first_head_gate
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (hN : 0<N) (s t A B : ℤ)
    (hA : s+1=A+(N:ℤ)+2) (hB : t+1=B+(N:ℤ)+1)
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (y : Ambient background T.Y (A,B))
    (hy : y ∈ cycles background T.Y ((N:ℤ)+2) (A,B))
    (hsource : (homotopyRegrade (show t-s+1=B-A by omega)
      (show (t-1-N)+1=B by omega)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ))≫
        (background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.Y A B y)
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v)
    (x : Ambient background T.X (s,t))
    (hx : Detects (background.convergence (.quotient 3 (.nu T.X))) (s,t,t-1)
      (finiteTargetLabel background T.X 3 s t 1 x)
      (((recursivePositiveBoundaryIso N s t).hom≫recursiveBoundaryRepresentative T.X N s t ζ)≫
        XModLambdaN.incl _ 3-c)) :
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y ((N:ℤ)+1) (s+1,t+1) := by
  have hd := recursive_positive_boundary_error_detects T hf N s t ζ c v hc x hx
  let η := homotopyRegrade (show t-s+1=B-A by omega) (show (t-1-N)+1=B by omega)
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ)
  let β := homotopyRegrade (show (t-s+1)-1=(t+1)-(s+1) by omega)
    (show ((t-1-N)+1)+N=(t+1)-1 by omega)
    (biSuspensionHomEquiv (t-s+1) ((t-1-N)+1) N
      (background.nu.functor.obj (T.Y.obj background.auxiliary))
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ≫
        XModLambdaN.proj _ N))
  have hβ : β=homotopyRegrade (show (B-A)-1=(t+1)-(s+1) by omega)
      (show B+N=(t+1)-1 by omega)
      (biSuspensionHomEquiv (B-A) B N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)) := by
    dsimp only [β,η]
    rw [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans]
  have hdet : Detects (background.convergence (.quotient 3 (.nu T.Y))) (s+1,t+1,(t+1)-1)
      (finiteTargetLabel background T.Y 3 (s+1) (t+1) 1
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x))
      (β≫XModLambdaN.incl _ 3) := by
    simpa only [β,←regrade_comp] using hd
  have hh := known_source_finite_label_boundary_at_degree T.Y N 1 3 hN (by decide) (by decide)
    A B (s+1) (t+1) ((N:ℤ)+3) (by omega) (by omega) (by omega) y η hsource
    (by simpa only [show (N:ℤ)+3-1=N+2 by omega] using hy) β hβ _ _ hdet
    (by rw [sub_self]; exact (background.syntheticTower.filtrationSubmodule _ _ _).zero_mem)
  simpa only [Nat.cast_add,Nat.cast_one] using hh

/-- The K1>1 positive head gate divides the same actual top-calibrated
source. The canonical absolute boundary is retained through division,
so the known-source cutoff applies to the actual recursive error head. -/
private theorem recursive_positive_divided_head_gate
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (d N : ℕ) (hd : 0<d) (hdN : d<N) (s t A B : ℤ)
    (hA : s+1=A+(N-d:ℕ)+2) (hB : t+1=B+(N-d:ℕ)+1)
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (y : Ambient background T.Y (A,B))
    (hy : y ∈ cycles background T.Y ((N-d:ℕ)+2) (A,B))
    (hsource : (homotopyRegrade (show t-s+1=B-A by omega)
      (show (t-1-N)+1=B-d by omega)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ))≫
        (background.quotients.tower _).rho (d+1) N (by omega)=finiteTopLabel T.Y d hd A B y)
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v)
    (x : Ambient background T.X (s,t))
    (hx : Detects (background.convergence (.quotient 3 (.nu T.X))) (s,t,t-1)
      (finiteTargetLabel background T.X 3 s t 1 x)
      (((recursivePositiveBoundaryIso N s t).hom≫recursiveBoundaryRepresentative T.X N s t ζ)≫
        XModLambdaN.incl _ 3-c)) :
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y ((N-d:ℕ)+1) (s+1,t+1) := by
  have hdet := recursive_positive_boundary_error_detects T hf N s t ζ c v hc x hx
  let η := homotopyRegrade (show t-s+1=B-A by omega) (show (t-1-N)+1=B-d by omega)
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s+1) (t-1-N) ζ)
  have htop : η≫(background.quotients.tower _).rho (d+1) N (by omega)=
      finiteTopLabelAtWeight T.Y d hd (d+1) rfl A B (B-d) rfl y := by
    simpa only [η,finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  have hb : Detects (background.convergence (.quotient 3 (.nu T.Y))) (s+1,t+1,(t+1)-1)
      (finiteTargetLabel background T.Y 3 (s+1) (t+1) 1
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x))
      (homotopyRegrade (show (B-A)-1=(t+1)-(s+1) by omega)
        (show (B-d)+N=(t+1)-1 by omega)
        (biSuspensionHomEquiv (B-A) (B-d) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)) := by
    dsimp only [η]
    rw [←regrade_comp,bi_susp_regrade,regrade_comp,normalized_homotopy_regrade_trans]
    simpa only [←regrade_comp] using hdet
  have hh := known_source_divided_boundary_detected_head T.Y d N (d+1) 1 3 hd hdN rfl
    (by decide) (by decide) A B (B-d) (s+1) (t+1) ((N-d:ℕ)+3) rfl (by omega) (by omega) (by omega)
    y (by simpa only [show ((N-d:ℕ):ℤ)+3-1=(N-d:ℕ)+2 by omega] using hy) η htop _ hb
  simpa only [Nat.cast_add,Nat.cast_one] using hh

end
end KIP126.ProofTools.Internal.SyntheticCoverage
