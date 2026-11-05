module

import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDifferential
import all KIP126.ProofTools.SyntheticCoverage.RawImageComparison

/-! Corrections of a fixed finite source by a prescribed earlier absolute
boundary. The selected coefficient insertion retains its actual suspension
comparison. The source sphere comparison is normalized explicitly before
insertion; at level one it acts trivially on the prescribed input itself. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private def boundarySourceSphereIso (m w i : ℤ) :
    Smn (Syn:=SyntheticSpectrum) m w ≅
      ((SyntheticCategory.biShift (0,-i)).obj (Smn (m-1) (w+i)))⟦(1:ℤ)⟧ := by
  let a := (biSuspensionHomEquiv m w i (Smn (Syn:=SyntheticSpectrum) (m-1) (w+i))).symm (𝟙 _)
  letI : IsIso a := by
    dsimp only [a]
    rw [bi_susp_symm_eq]
    letI : IsIso (susp_invariance (m-1) (w+i) 1 (-i)
        (Smn (Syn:=SyntheticSpectrum) (m-1) (w+i)) (𝟙 _)) := by
      change IsIso (((SyntheticCategory.biShift_comp (m-1,w+i) (1,-i)).inv.app S_0_0) ≫
        (SyntheticCategory.biShift (1,-i)).map (𝟙 (Smn (m-1) (w+i))) ≫ 𝟙 _)
      erw [CategoryTheory.Functor.map_id,Category.comp_id,Category.comp_id]
      exact inferInstanceAs (IsIso (((SyntheticCategory.biShift_comp
        (Syn:=SyntheticSpectrum) (m-1,w+i) (1,-i)).app S_0_0).inv))
    letI := regrade_isIso (show (m-1)+1=m by omega)
      (show (w+i)+(-i)=w by omega)
      (susp_invariance (m-1) (w+i) 1 (-i)
        (Smn (Syn:=SyntheticSpectrum) (m-1) (w+i)) (𝟙 _))
    exact inferInstance
  exact asIso a

private theorem boundary_suspension_eq_source_iso (A : SyntheticSpectrum)
    (m w i : ℤ) (a : BiHom (m-1) (w+i) A) :
    (biSuspensionHomEquiv m w i A).symm a =
      (boundarySourceSphereIso m w i).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map a) := by
  simpa only [boundarySourceSphereIso,asIso_hom,Category.id_comp] using
    bi_susp_symm_natural m w i a (𝟙 _)

private def boundaryLiftSourceIso (m w i : ℤ)
    (u : Smn (Syn:=SyntheticSpectrum) (m-1) (w+i) ≅ Smn (m-1) (w+i)) :
    Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w :=
  boundarySourceSphereIso m w i ≪≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((SyntheticCategory.biShift (0,-i)).mapIso u) ≪≫
    (boundarySourceSphereIso m w i).symm

private theorem boundary_lift_source_precomp (A : SyntheticSpectrum)
    (m w i : ℤ)
    (u : Smn (Syn:=SyntheticSpectrum) (m-1) (w+i) ≅ Smn (m-1) (w+i))
    (a : BiHom m w (((SyntheticCategory.biShift (0,-i)).obj A)⟦(1:ℤ)⟧)) :
    biSuspensionHomEquiv m w i A ((boundaryLiftSourceIso m w i u).hom ≫ a) =
      u.hom ≫ biSuspensionHomEquiv m w i A a := by
  apply (biSuspensionHomEquiv m w i A).symm.injective
  rw [AddEquiv.symm_apply_apply,boundary_suspension_eq_source_iso]
  have ha := boundary_suspension_eq_source_iso A m w i (biSuspensionHomEquiv m w i A a)
  rw [AddEquiv.symm_apply_apply] at ha
  conv_lhs => rw [ha]
  simp only [boundaryLiftSourceIso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,
    Functor.map_comp,Category.assoc,Iso.inv_hom_id_assoc]

/-- Coefficient insertion with the actual boundary comparison normalized
at the source sphere. This uses the given class, at every finite level. -/
private def boundaryNormalizedInsertion (X : (AdamsObject (coefficients := background.coefficients)))
    (d N : ℕ) (hd : 0<d) (hdN : d<N) (m t : ℤ)
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d))) :
    BiHom m (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N) :=
  let u := boundaryDivisionSourceIso d N hdN.le m t
  let v := boundaryLiftSourceIso m t (N-d:ℕ) u.symm
  let b := v.hom ≫ a
  verticalShiftEquiv _ d m (t-d) (homotopyRegrade rfl (show t=(t-d)+d by omega) b) ≫
    ((background.quotients.tower _).triangle hd hdN).lambdaMap

private theorem boundary_normalized_insertion_boundary (X : (AdamsObject (coefficients := background.coefficients)))
    (d N : ℕ) (hd : 0<d) (hdN : d<N) (m t : ℤ)
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d))) :
    homotopyRegrade rfl (show (t-d)+N=t+(N-d:ℕ) by omega)
      (biSuspensionHomEquiv m (t-d) N (background.nu.functor.obj (X.obj background.auxiliary))
        (boundaryNormalizedInsertion X d N hd hdN m t a ≫ XModLambdaN.proj _ N)) =
      biSuspensionHomEquiv m t (N-d:ℕ) (background.nu.functor.obj (X.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ (N-d)) := by
  dsimp only [boundaryNormalizedInsertion]
  rw [divided_boundary_eq_reindex,boundaryDivisionReindex_eq_precomp,Category.assoc,
    boundary_lift_source_precomp]
  simp only [Iso.symm_hom,Iso.hom_inv_id_assoc]

private theorem boundary_normalized_insertion_first_zero (X : (AdamsObject (coefficients := background.coefficients)))
    (d N : ℕ) (hd : 0<d) (hdN : d<N) (m t : ℤ)
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d))) :
    boundaryNormalizedInsertion X d N hd hdN m t a ≫
      (background.quotients.tower _).rho 1 N (by omega) = 0 := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let C := (background.quotients.tower A).triangle hd hdN
  have hz : C.lambdaMap ≫ (background.quotients.tower A).rho d N hdN.le = 0 := by
    rw [←(background.quotients.tower A).triangle_rho hd hdN]
    exact comp_distTriang_mor_zero₁₂ _ C.distinguished
  dsimp only [boundaryNormalizedInsertion]
  rw [←(background.quotients.tower _).rho_comp (show 1≤d by omega) hdN.le]
  simp only [Category.assoc]
  rw [←Category.assoc (((background.quotients.tower A).triangle hd hdN).lambdaMap),hz,
    zero_comp,comp_zero]

/-- Subtracting the earlier coefficient boundary preserves the specified
first restriction and subtracts exactly the specified full boundary. -/
private theorem finite_source_correction_of_earlier_boundary (X : (AdamsObject (coefficients := background.coefficients)))
    (d N : ℕ) (hd : 0<d) (hdN : d<N) (m t : ℤ)
    (z : BiHom m (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d))) :
    ∃ η : BiHom m (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      η ≫ (background.quotients.tower _).rho 1 N (by omega) =
        z ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      homotopyRegrade rfl (show (t-d)+N=t+(N-d:ℕ) by omega)
          (biSuspensionHomEquiv m (t-d) N (background.nu.functor.obj (X.obj background.auxiliary))
            (η ≫ XModLambdaN.proj _ N)) =
        homotopyRegrade rfl (show (t-d)+N=t+(N-d:ℕ) by omega)
          (biSuspensionHomEquiv m (t-d) N (background.nu.functor.obj (X.obj background.auxiliary))
            (z ≫ XModLambdaN.proj _ N)) -
        biSuspensionHomEquiv m t (N-d:ℕ) (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ (N-d)) := by
  refine ⟨z-boundaryNormalizedInsertion X d N hd hdN m t a,?_,?_⟩
  · rw [Preadditive.sub_comp,boundary_normalized_insertion_first_zero,sub_zero]
  · rw [Preadditive.sub_comp,map_sub,homotopy_regrade_sub,boundary_normalized_insertion_boundary]

/-- At level one the source automorphism acts trivially on the specified Q₁ class. -/
private theorem boundary_normalized_insertion_one (X : (AdamsObject (coefficients := background.coefficients)))
    (d N : ℕ) (hd : 0<d) (hdN : d<N) (hlevel : N-d=1) (m t : ℤ)
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d))) :
    boundaryNormalizedInsertion X d N hd hdN m t a =
      verticalShiftEquiv _ d m (t-d) (homotopyRegrade rfl (show t=(t-d)+d by omega) a) ≫
        ((background.quotients.tower _).triangle hd hdN).lambdaMap := by
  have hfix (q : ℕ) (hq : q=1)
      (b : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
      (v : Smn (Syn:=SyntheticSpectrum) m t ≅ Smn m t) : v.hom ≫ b=b := by
    subst q
    exact sphere_automorphism_first_finite X m t v b
  dsimp only [boundaryNormalizedInsertion]
  rw [hfix (N-d) hlevel]

/-- Correction with independent displayed length and weight on the given
finite quotient and input. -/
private theorem finite_source_correction_of_earlier_boundary_at_weight (X : (AdamsObject (coefficients := background.coefficients)))
    (d N i : ℕ) (hd : 0<d) (hdN : d<N) (hlevel : N-d=i)
    (m w t : ℤ) (hw : w=t-d)
    (z : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i)) :
    ∃ η : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      η ≫ (background.quotients.tower _).rho 1 N (by omega) =
        z ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      homotopyRegrade rfl (show w+N=t+i by omega)
          (biSuspensionHomEquiv m w N (background.nu.functor.obj (X.obj background.auxiliary))
            (η ≫ XModLambdaN.proj _ N)) =
        homotopyRegrade rfl (show w+N=t+i by omega)
          (biSuspensionHomEquiv m w N (background.nu.functor.obj (X.obj background.auxiliary))
            (z ≫ XModLambdaN.proj _ N)) -
        biSuspensionHomEquiv m t i (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ i) := by
  subst i
  subst w
  exact finite_source_correction_of_earlier_boundary X d N hd hdN m t z a

private theorem positive_early_source_first
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (hN : 0<N) (s t : ℤ) (x : Ambient background T.X (s,t))
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hz : z ≫ (background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.X s t x) :
    homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t z ≫
        (background.quotients.tower _).rho 1 N hN) =
      nativeFirstLabel T.Y (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) := by
  rw [positive_finite_image_restriction T hf 1 N (by decide) hN,hz]
  have hs : positiveFiniteImage T hf 1 (levelQuotientShiftIso T.X 1 1)
      (t-s) t (nativeFirstLabel T.X s t x) =
      (background.firstQuotient T.X 1 s t).symm x ≫
        XModLambdaN.map (lastLayerNormalizedMap T hf) 1 := by
    rw [←positive_first_label_shift T.X s t x]
    simp [positiveFiniteImage,verticalTranslate,regradeAddEquiv,
      suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,
      Iso.homCongr,regrade_comp,Category.assoc]
  rw [hs]
  exact normalizedFirstMap_boundary T hf s t x

private theorem positive_early_source_boundary
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega)
      (show (t+1)+N=(t+N)+1 by omega)
      (biSuspensionHomEquiv (t-s) (t+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t z ≫
          XModLambdaN.proj _ N)) =
      verticalTranslate _ 1 ((t+N)-(s+N+1)) (t+N) (positiveAdjustedBoundary T.X N s t z) ≫
        lastLayerNormalizedMap T hf := by
  have himage : positiveBoundaryFiniteImage T.X T.Y (lastLayerNormalizedMap T hf) N s t z =
      homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
        (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t z) := by
    simp [positiveBoundaryFiniteImage,positiveFiniteImage,verticalTranslate,
      regradeAddEquiv,suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,
      Iso.homCongr,regrade_comp,Category.assoc]
  have hb := positive_boundary_finite_image_boundary T.X T.Y (lastLayerNormalizedMap T hf) N s t z
  rw [himage] at hb
  dsimp only [boundaryRepresentative] at hb
  rw [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans] at hb
  have h := congrArg (homotopyRegrade
    (show ((t+1)+N)-((s+1)+N+1)=(t+N)-(s+N+1) by omega)
    (show (t+1)+N=(t+N)+1 by omega)) hb
  simpa only [normalized_homotopy_regrade_trans,top_target_regrade_self] using h

/-- A given earlier boundary corrects the positive image of the same source.
The resulting finite source has exactly F₂x as its first label, and its full
boundary is the actual normalized image minus that prescribed boundary. -/
private theorem positive_source_correction_of_earlier_boundary
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N i : ℕ) (hi : 0 < i) (hiN : i < N) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hz : z ≫ (background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel T.X s t x)
    (ahat : BiHom (t-s) ((t+1)+N-i)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i)) :
    ∃ η : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
          (η ≫ (background.quotients.tower _).rho 1 N (by omega)) =
        nativeFirstLabel T.Y (s+1) (t+1)
          (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
      homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega)
          (show (t+1)+N=(t+N)+1 by omega)
          (biSuspensionHomEquiv (t-s) (t+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (η ≫ XModLambdaN.proj _ N)) =
        (verticalTranslate _ 1 ((t+N)-(s+N+1)) (t+N) (positiveAdjustedBoundary T.X N s t z) ≫
          lastLayerNormalizedMap T hf) -
        homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega)
          (show (((t+1)+N-i)+i)=(t+N)+1 by omega)
          (biSuspensionHomEquiv (t-s) ((t+1)+N-i) i (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (ahat ≫ XModLambdaN.proj _ i)) := by
  obtain ⟨η,hη,hboundary⟩ := finite_source_correction_of_earlier_boundary_at_weight
    T.Y (N-i) N i (by omega) (by omega) (by omega) (t-s) (t+1) ((t+1)+N-i) (by omega)
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t z) ahat
  refine ⟨η,?_,?_⟩
  · rw [hη]
    exact positive_early_source_first T hf N (by omega) s t x z hz
  · have h := congrArg (homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega)
      (show (((t+1)+N-i)+i)=(t+N)+1 by omega)) hboundary
    simpa only [homotopy_regrade_sub,normalized_homotopy_regrade_trans,
      positive_early_source_boundary] using h

end
end KIP126.ProofTools.Internal.SyntheticCoverage
