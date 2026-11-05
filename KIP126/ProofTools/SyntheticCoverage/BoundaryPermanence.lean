module

public import KIP126.ProofTools.Language

import all KIP126.ProofTools.SyntheticCoverage.LambdaTranslate
import all KIP126.ProofTools.SyntheticCoverage.StrictSource
import all KIP126.ProofTools.SyntheticCoverage.Permanence
import all KIP126.ProofTools.GeneralizedMahowald.CumulativeBoundary

/-! Absolute-boundary correction for permanence criteria. The correction
preserves the finite differential representative, its first label,
and the realization of the full image. Mapping the representative
to the adjacent quotient gives a lambda-kernel ambiguity in the
early-boundary subgroup; the quotient-kernel condition identifies
the permanent candidate. The prescribed-source cases cover all first/second
normalizations in {0,1}. A positive second map retains the quotient-shift
source automorphism in its torsion correction. General nonnegative
normalizations are treated separately. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem absolute_boundary_lambda_zero (A : SyntheticSpectrum)
    (m w : ℤ) (q : ℕ) (c : BiHom m w (XModLambdaN A q)) :
    lambdaMultiply q (biSuspensionHomEquiv m w q A (c≫XModLambdaN.proj A q))=0 := by
  let a := biSuspensionHomEquiv m w q A (c≫XModLambdaN.proj A q)
  have hδ : ((biSuspensionHomEquiv m w q A).symm a)≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q A)=0 := by
    simp only [a,AddEquiv.symm_apply_apply,Category.assoc]
    have hz := comp_distTriang_mor_zero₃₁ (XModLambdaN.cofiberTriangle A q)
      (XModLambdaN.cofiberTriangle_distinguished A q)
    change XModLambdaN.proj A q≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q A)=0 at hz
    rw [hz,comp_zero]
  have hmap := (shifted_representative_zero_iff m w q A A (lambdaPow q A) a).mp hδ
  have hraw : lambdaPow q (Smn (m-1) (w+q))≫a=0 :=
    (lambdaPow_naturality q a).symm.trans hmap
  change lambdaMultiply q a=0
  simp only [lambdaMultiply,hraw,comp_zero]

private theorem boundary_representative_lambda_zero (Y : (AdamsObject (coefficients := background.coefficients)))
    (q : ℕ) (s t : ℤ)
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    lambdaMultiply q (boundaryRepresentative Y q s t c)=0 := by
  dsimp only [boundaryRepresentative]
  rw [lambda_regrade,absolute_boundary_lambda_zero]
  simp only [regrade_precomp,comp_zero]

/-- Every full class of finite lambda-torsion realizes to zero in the chosen coordinates. -/
private theorem lambda_torsion_realization_zero
    (R : RealizationCoordinates background) {A : SyntheticSpectrum}
    (m w : ℤ) (k : ℕ) (a : BiHom m w A) (ha : lambdaMultiply k a=0) :
    (R.sphere m w).hom≫background.recovery.realization.map a=0 := by
  letI := R.additive
  have h := realization_lambda_multiply R m w k a
  rw [ha,Functor.map_zero,comp_zero] at h
  exact h.symm

/-- Subtracting an actual lambda-torsion correction whose first quotient
matches the prescribed full image makes that image divisible by lambda.
The quotient preimage realizes to the same full image. -/
private theorem torsion_corrected_full_image
    (R : RealizationCoordinates background) (Y : (AdamsObject (coefficients := background.coefficients)))
    (m t : ℤ) (k : ℕ)
    (a T : BiHom m (t-1) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hfirst : a≫XModLambdaN.incl _ 1=T≫XModLambdaN.incl _ 1)
    (hT : lambdaMultiply k T=0) :
    ∃ b : BiHom m t (background.nu.functor.obj (Y.obj background.auxiliary)),
      lambdaMultiply 1 b = a-T ∧
      (R.sphere m t).hom≫background.recovery.realization.map b =
        (R.sphere m (t-1)).hom≫background.recovery.realization.map a := by
  letI := R.additive
  have hz : (a-T)≫XModLambdaN.incl _ 1=0 := by
    rw [Preadditive.sub_comp,hfirst,sub_self]
  obtain ⟨b,hb⟩ := full_image_lambda_preimage_native (𝟙 _) m t (a-T)
    (by simpa only [Category.comp_id] using hz)
  simp only [Category.comp_id] at hb
  have hrealT := lambda_torsion_realization_zero R m (t-1) k T hT
  have hl := realization_lambda_multiply R m t 1 b
  rw [hb,Functor.map_sub,Preadditive.comp_sub] at hl
  change (R.sphere m (t-1)).hom≫background.recovery.realization.map a -
    (R.sphere m (t-1)).hom≫background.recovery.realization.map T = _ at hl
  rw [hrealT,sub_zero] at hl
  exact ⟨b,hb,hl.symm⟩

/-- The specified differential source produces the absolute boundary
and finite representative used by the next triangle map. -/
private theorem differential_torsion_correction
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : Ambient background Y (s,t)) (y : Ambient background Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a y)
    (image : BiHom ((t+q)-(s+q+1)) (t+q)
      (background.nu.functor.obj (Y.obj background.auxiliary)))
    (himage : image≫XModLambdaN.incl _ 1=nativeFirstLabel Y (s+q+1) (t+q) y) :
    ∃ z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q),
      z≫(background.quotients.tower _).rho 1 q hq=nativeFirstLabel Y s t a ∧
      boundaryRepresentative Y q s t z≫XModLambdaN.incl _ 1=
        nativeFirstLabel Y (s+q+1) (t+q) y ∧
      lambdaMultiply q (boundaryRepresentative Y q s t z)=0 ∧
      ∃ b : BiHom ((t+q)-(s+q+1)) (t+q+1)
          (background.nu.functor.obj (Y.obj background.auxiliary)),
        homotopyRegrade rfl (show (t+q+1)-(1:ℕ)=t+q by omega) (lambdaMultiply 1 b)=
          image-boundaryRepresentative Y q s t z ∧
        ∃ w : Ambient background Y (s+q+2,t+q+1),
          (homotopyRegrade (by omega) rfl b)≫XModLambdaN.incl _ 1=
            nativeFirstLabel Y (s+q+2) (t+q+1) w ∧
          w∈permanentCycles background Y (s+q+2,t+q+1) ∧
          ClassicalDetects (background.classicalConvergence Y) (s+q+2,t+q+1) w
            (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
              (t+q+1)-(s+q+2)=(t+q)-(s+q+1))) ≫
              (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
                background.recovery.realization.map image≫(hcomp.nu Y).target.hom) := by
  obtain ⟨z,hz,hzy⟩ := (differential_iff_specified_adjacent_lift Y q hq s t a y).mp hd
  have hT := boundary_representative_lambda_zero Y q s t z
  let m := (t+q)-(s+q+1)
  let T := boundaryRepresentative Y q s t z
  let image' : BiHom m ((t+q+1)-1) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade rfl (by omega) image
  let T' : BiHom m ((t+q+1)-1) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade rfl (by omega) T
  have hfirst : image'≫XModLambdaN.incl _ 1=T'≫XModLambdaN.incl _ 1 := by
    dsimp only [image',T']
    rw [←regrade_comp,←regrade_comp,himage]
    exact congrArg (homotopyRegrade rfl (by omega)) hzy.symm
  have hT' : lambdaMultiply q T'=0 := by
    dsimp only [T']
    rw [lambda_regrade,hT]
    simp only [regrade_precomp,comp_zero]
  obtain ⟨b',hb,hreal⟩ := torsion_corrected_full_image R Y m (t+q+1) q image' T' hfirst hT'
  let b'' : BiHom ((t+q+1)-(s+q+2)) (t+q+1)
      (background.nu.functor.obj (Y.obj background.auxiliary)) := homotopyRegrade (by dsimp [m]; omega) rfl b'
  obtain ⟨w,hw,hwp,hwd⟩ := full_representative_first_label_detects R hcomp Y
    (s+q+2) (t+q+1) b''
  refine ⟨z,hz,hzy,hT,b',?_,w,hw,hwp,?_⟩
  · rw [hb]
    simp only [image',T',T,m,regrade_precomp,Preadditive.comp_sub,←Category.assoc,
      eqToHom_trans,eqToHom_refl,Category.id_comp]
  · have hbReal := realization_homotopy_regrade_full R
      (by dsimp [m]; omega : m=(t+q+1)-(s+q+2)) rfl b'
    have hiReal := realization_homotopy_regrade_full R rfl
      (by omega : t+q=(t+q+1)-1) image
    have hh : (R.sphere ((t+q+1)-(s+q+2)) (t+q+1)).hom≫
        background.recovery.realization.map b'' =
        eqToHom (congrArg (Sphere (C:=Spectrum)) (by dsimp [m]; omega :
          (t+q+1)-(s+q+2)=m))≫
          (R.sphere m (t+q)).hom≫background.recovery.realization.map image := by
      change (R.sphere _ _).hom≫background.recovery.realization.map
        (homotopyRegrade _ rfl b') = _
      rw [hbReal,hreal]
      dsimp only [image']
      rw [hiReal]
      simp only [eqToHom_refl,Category.id_comp]
      rfl
    have hhh := congrArg (fun z => z≫(hcomp.nu Y).target.hom) hh
    simp only [Category.assoc] at hhh
    exact hhh ▸ hwd

/-- Vanishing of the absolute boundary in Q₁ lifts the specified
finite representative to the adjacent quotient. -/
private theorem adjacent_lift_of_boundary_first_zero
    (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hz : boundaryRepresentative X q s t z≫XModLambdaN.incl _ 1=0) :
    ∃ e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1)),
      e≫(background.quotients.tower _).rho q (q+1) (by omega)=z := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let T := (background.quotients.tower A).triangle hq (Nat.lt_succ_self q)
  have hraw : (biSuspensionHomEquiv (t-s) t q A (z≫XModLambdaN.proj A q))≫
      XModLambdaN.incl A 1=0 := by
    have hh : homotopyRegrade (show t-s-1=(t+q)-(s+q+1) by omega) rfl
        ((biSuspensionHomEquiv (t-s) t q A (z≫XModLambdaN.proj A q))≫
          XModLambdaN.incl A 1)=0 := by
      simpa only [boundaryRepresentative,regrade_comp] using hz
    exact (homotopy_regrade_eq_zero _ _ _).mp hh
  have hdelta : z≫T.delta=0 := by
    apply (biSuspensionHomEquiv (t-s) t q (XModLambdaN A ((q+1)-q))).injective
    rw [map_zero]
    rw [cofiber_boundary_projection X q (q+1) hq (Nat.lt_succ_self q)]
    have transport (j : ℕ) (hj : j=1)
        (b : BiHom (t-s-1) (t+q) A) (hb : b≫XModLambdaN.incl A 1=0) :
        b≫XModLambdaN.incl A j=0 := by subst j; exact hb
    exact transport ((q+1)-q) (by omega) _ hraw
  obtain ⟨e,he⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₃ T.distinguished z hdelta
  refine ⟨e,?_⟩
  rw [←(background.quotients.tower A).triangle_rho hq (Nat.lt_succ_self q)]
  exact he.symm

/-- The adjacent lift retains the prescribed Q₁ source and relates the two
absolute boundaries by multiplication by exactly one lambda. -/
private theorem adjacent_lift_boundary_relation
    (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hz : boundaryRepresentative X q s t z≫XModLambdaN.incl _ 1=0) :
    ∃ e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1)),
      e≫(background.quotients.tower _).rho q (q+1) (by omega)=z ∧
      e≫(background.quotients.tower _).rho 1 (q+1) (by omega)=
        z≫(background.quotients.tower _).rho 1 q hq ∧
      boundaryRepresentative X q s t z =
        homotopyRegrade (by omega) (by omega)
          (lambdaMultiply ((q+1)-q) (boundaryRepresentative X (q+1) s t e)) := by
  obtain ⟨e,he⟩ := adjacent_lift_of_boundary_first_zero X q hq s t z hz
  refine ⟨e,he,?_,?_⟩
  · rw [←he,Category.assoc,(background.quotients.tower _).rho_comp hq (show q≤q+1 by omega)]
  · have h := absolute_boundary_restriction X q (q+1) (by omega) (t-s) t e
    rw [he] at h
    have hh := congrArg (homotopyRegrade (show t-s-1=(t+q)-(s+q+1) by omega) rfl) h
    simpa only [boundaryRepresentative,lambda_regrade,normalized_homotopy_regrade_trans] using hh

/-- The lambda kernel and the ambiguity of finite lifts with the same first
label are early boundaries. This identifies the denominator of the
quotient-kernel condition for absolute-boundary permanence. -/
private theorem adjacent_lambda_error_is_boundary
    (Z : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (U : Ambient background Z (s,t)) (v w : Ambient background Z (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (eta : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) (q+1)))
    (heta : eta≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel Z s t U)
    (b : BiHom ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)) (t+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Z.obj background.auxiliary)))
    (hb : b≫XModLambdaN.incl _ 1=nativeFirstLabel Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) w)
    (herr : lambdaMultiply 1 (b+boundaryRepresentative Z (q+1) s t eta)=0)
    (hd : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      ((q+1)+1) (s,t) (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)) U v) :
    w-v ∈ boundaries background Z (q+1) (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)) := by
  obtain ⟨eta',heta',hv⟩ := (differential_iff_specified_adjacent_lift Z (q+1)
    (by omega) s t U v).mp hd
  have hfirst : (eta-eta')≫(background.quotients.tower _).rho 1 (q+1) (by omega)=0 := by
    rw [Preadditive.sub_comp,heta,heta',sub_self]
  have hdiff := first_restriction_kernel_boundary_lambda_zero Z (q+1) (by omega)
    s t (eta-eta') hfirst
  simp only [boundaryRepresentative_sub] at hdiff
  have hdiff' : lambdaMultiply q (boundaryRepresentative Z (q+1) s t eta-
      boundaryRepresentative Z (q+1) s t eta')=0 := by
    exact hdiff
  have hsum := lambdaMultiply_zero_of_le ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)) (t+((q+1:ℕ):ℤ))
    1 q (by omega) (b+boundaryRepresentative Z (q+1) s t eta) herr
  have htotal : lambdaMultiply q (b+boundaryRepresentative Z (q+1) s t eta')=0 := by
    have he : b+boundaryRepresentative Z (q+1) s t eta' =
      (b+boundaryRepresentative Z (q+1) s t eta)-
        (boundaryRepresentative Z (q+1) s t eta-boundaryRepresentative Z (q+1) s t eta') := by abel
    rw [he]
    simp only [lambdaMultiply,Preadditive.comp_sub] at hsum hdiff' ⊢
    rw [hsum,hdiff',sub_self]
  have hvneg : -v=v := neg_eq_of_add_eq_zero_left
    (classical_page_two (Z.obj background.auxiliary) 2 (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)) v)
  have hlabel : (b+boundaryRepresentative Z (q+1) s t eta')≫XModLambdaN.incl _ 1 =
      nativeFirstLabel Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) (w-v) := by
    rw [Preadditive.add_comp,hb]
    change _+adjacentBoundaryLabel Z (q+1) s t eta'=_
    rw [hv]
    have hsub := firstLabel_sub Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) w v
    dsimp only [nativeFirstLabel]
    rw [hsub,Preadditive.sub_comp]
    have hnv : -(nativeFirstLabel Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) v)=
        nativeFirstLabel Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) v := by
      have ht : nativeFirstLabel Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) (-v)=
          -(nativeFirstLabel Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) v) := by
        simp only [nativeFirstLabel,first_label_inline,map_neg,regrade_precomp,Preadditive.comp_neg,
          Preadditive.neg_comp]
      rw [hvneg] at ht
      exact ht.symm
    exact (sub_eq_add_neg (nativeFirstLabel Z _ _ w) (nativeFirstLabel Z _ _ v)).trans
      (congrArg (fun z => nativeFirstLabel Z _ _ w+z) hnv) |>.symm
  exact first_label_lambda_zero_boundary Z (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) q hq (w-v)
    (b+boundaryRepresentative Z (q+1) s t eta') hlabel htotal

private theorem boundary_representative_natural
    (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (g : background.nu.functor.obj (Y.obj background.auxiliary) ⟶ background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    boundaryRepresentative Z q s t (z≫XModLambdaN.map g q)=
      boundaryRepresentative Y q s t z≫g := by
  dsimp only [boundaryRepresentative]
  rw [Category.assoc,XModLambdaN.proj_naturality,←Category.assoc]
  rw [bi_susp_natural background.quotients.coherence,regrade_comp]

/-- Apply the second actual map to the same correction representative.
The zero composite lifts its quotient image one layer further and yields
the precise lambda-kernel equation used by the early-boundary comparison. -/
private theorem mapped_correction_adjacent_lift
    (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (g : background.nu.functor.obj (Y.obj background.auxiliary) ⟶ background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (b : BiHom ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)) (t+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hfirst : image≫XModLambdaN.incl _ 1=
      boundaryRepresentative Y q s t z≫XModLambdaN.incl _ 1)
    (hzero : image≫g=0)
    (hcorr : homotopyRegrade (by omega) (by omega) (lambdaMultiply 1 b)=
      image-boundaryRepresentative Y q s t z) :
    ∃ eta : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) (q+1)),
      eta≫(background.quotients.tower _).rho q (q+1) (by omega)=z≫XModLambdaN.map g q ∧
      eta≫(background.quotients.tower _).rho 1 (q+1) (by omega)=
        (z≫XModLambdaN.map g q)≫(background.quotients.tower _).rho 1 q hq ∧
      lambdaMultiply 1 (b≫g+boundaryRepresentative Z (q+1) s t eta)=0 := by
  have hz : boundaryRepresentative Z q s t (z≫XModLambdaN.map g q)≫XModLambdaN.incl _ 1=0 := by
    rw [boundary_representative_natural,Category.assoc,XModLambdaN.incl_naturality,
      ←Category.assoc,←hfirst,Category.assoc,←XModLambdaN.incl_naturality,
      ←Category.assoc,hzero,zero_comp]
  obtain ⟨eta,he,hefirst,hd⟩ := adjacent_lift_boundary_relation Z q hq s t
    (z≫XModLambdaN.map g q) hz
  refine ⟨eta,he,hefirst,?_⟩
  have hqdiff : (q+1)-q=1 := by omega
  have hd' : boundaryRepresentative Z q s t (z≫XModLambdaN.map g q)=
      homotopyRegrade (by omega) (by omega)
        (lambdaMultiply 1 (boundaryRepresentative Z (q+1) s t eta)) := by
    have transform (k : ℕ) (hk : k=1)
        (a : BiHom ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)) (t+((q+1:ℕ):ℤ))
          (background.nu.functor.obj (Z.obj background.auxiliary)))
        (hh : ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1))=((t+q)-(s+q+1)))
        (hw : t+((q+1:ℕ):ℤ)-(k:ℤ)=t+q) :
        homotopyRegrade hh hw (lambdaMultiply k a)=
          homotopyRegrade hh (by omega) (lambdaMultiply 1 a) := by subst k; rfl
    exact hd.trans (transform _ hqdiff _ _ _)
  rw [boundary_representative_natural] at hd'
  have hmap := congrArg (fun a => a≫g) hcorr
  rw [Preadditive.sub_comp,hzero,zero_sub,hd'] at hmap
  have herr : homotopyRegrade (by omega :
      (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q)-(s+q+1))
      (by omega : t+((q+1:ℕ):ℤ)-(1:ℕ)=t+q)
      (lambdaMultiply 1 (b≫g+boundaryRepresentative Z (q+1) s t eta))=0 := by
    simp only [lambdaMultiply,Preadditive.comp_add,regrade_precomp,Preadditive.comp_add]
    have hh := hmap
    simp only [lambdaMultiply,regrade_precomp,Category.assoc] at hh
    rw [hh,neg_add_cancel]
  exact (homotopy_regrade_eq_zero _ _ _).mp herr

/-- Full-image absolute-boundary permanence for an ordinary second map.
The two differentials give the correction and comparison; the complete
quotient kernel identifies the permanent class using the zero composite. -/
private theorem ordinary_boundary_lift_full_image
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : Ambient background Y (s,t)) (y : Ambient background Y (s+q+1,t+q))
    (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a y)
    (hd' : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      ((q+1)+1) (s,t) (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))
      ((background.classical.map g).pageMap 2 (s,t) a)
      ((background.classical.map g).pageMap 2 _ v))
    (image : BiHom ((t+q)-(s+q+1)) (t+q)
      (background.nu.functor.obj (Y.obj background.auxiliary)))
    (himage : image≫XModLambdaN.incl _ 1=nativeFirstLabel Y (s+q+1) (t+q) y)
    (hzero : image≫background.nu.functor.map g=0)
    (P : Submodule ℤ (Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → (background.classical.map g).pageMap 2 _ z ∈
      boundaries background Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ z) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q)-(s+q+1)))≫
          (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
            background.recovery.realization.map image≫(hcomp.nu Y).target.hom) := by
  obtain ⟨z,hz,hzy,hT,b,hb,w,hw,hwp,hwd⟩ :=
    differential_torsion_correction R hcomp Y q hq s t a y hd image himage
  let b' : BiHom ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)) (t+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Y.obj background.auxiliary)) := homotopyRegrade (by omega) (by omega) b
  have hcorr : homotopyRegrade (by omega) (by omega) (lambdaMultiply 1 b')=
      image-boundaryRepresentative Y q s t z := by
    simpa only [b',lambda_regrade,normalized_homotopy_regrade_trans] using hb
  obtain ⟨eta,heta,heta1,herr⟩ := mapped_correction_adjacent_lift Y Z
    (background.nu.functor.map g) q hq s t z image b' (himage.trans hzy.symm) hzero hcorr
  have heU : eta≫(background.quotients.tower _).rho 1 (q+1) (by omega)=
      nativeFirstLabel Z s t ((background.classical.map g).pageMap 2 (s,t) a) := by
    rw [heta1,Category.assoc,←(background.quotients.natural (background.nu.functor.map g)).rho_naturality,
      ←Category.assoc,hz,native_first_label_natural]
  obtain ⟨w',hw',hwp',hwd'⟩ := full_representative_first_label_detects R hcomp Y
    (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) b'
  have hbG : (b'≫background.nu.functor.map g)≫XModLambdaN.incl _ 1 =
      nativeFirstLabel Z _ _ ((background.classical.map g).pageMap 2 _ w') := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hw',native_first_label_natural]
  have hdiff := adjacent_lambda_error_is_boundary Z q hq s t _ _ _ eta heU
    (b'≫background.nu.functor.map g) hbG herr hd'
  have hdet : ClassicalDetects (background.classicalConvergence Y) _ w'
      (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
        (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q)-(s+q+1)))≫
        (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
          background.recovery.realization.map image≫(hcomp.nu Y).target.hom) := by
    have hreal := realization_homotopy_regrade_full R
      (by omega : (t+q)-(s+q+1)=(t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1))
      (by omega : t+q+1=t+((q+1:ℕ):ℤ)) b
    have hbc := realization_lambda_multiply R ((t+q)-(s+q+1)) (t+q+1) 1 b
    have hbc' := realization_homotopy_regrade_full R rfl
      (show (t+q+1)-(1:ℕ)=t+q by omega) (lambdaMultiply 1 b)
    rw [hb] at hbc'
    letI := R.additive
    have hTZ := lambda_torsion_realization_zero R _ _ q (boundaryRepresentative Y q s t z) hT
    simp only [eqToHom_refl,Category.id_comp,Functor.map_sub,Preadditive.comp_sub,hTZ,sub_zero] at hbc'
    rw [hbc] at hbc'
    have hr := congrArg (fun e => e≫(hcomp.nu Y).target.hom) hreal
    simp only [Category.assoc] at hr
    have hbc'' := congrArg (fun e => e≫(hcomp.nu Y).target.hom) hbc'
    simp only [Category.assoc] at hbc''
    rw [←hbc''] at hr
    exact hr ▸ hwd'
  exact classical_detects_of_quotient_kernel Y _
    ((background.classical.map g).pageMap 2 _).hom.toAddMonoidHom
    (boundaries background Z (q+1) _).toAddSubgroup P.toAddSubgroup
    hkernel w' v (hP hwp') hvP hdiff _ hdet

/-- Absolute-boundary permanence for ordinary first and second maps.
Every class strictly detected by x gives a permanent candidate detecting
its f-image. The triangle supplies the displayed zero composite of
the native synthetic maps. -/
private theorem ordinary_boundary_lift_prescribed_source
    (X Y Z : (AdamsObject (coefficients := background.coefficients)))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (hfg : background.nu.functor.map f≫background.nu.functor.map g=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background X (s+q+1,t+q))
    (a : Ambient background Y (s,t))
    (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a ((background.classical.map f).pageMap 2 _ x))
    (hd' : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      ((q+1)+1) (s,t) (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))
      ((background.classical.map g).pageMap 2 (s,t) a)
      ((background.classical.map g).pageMap 2 _ v))
    (P : Submodule ℤ (Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → (background.classical.map g).pageMap 2 _ z ∈
      boundaries background Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ z)
    (ξ : HomotopyGroup ((t+q)-(s+q+1)) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s+q+1,t+q) x)
    (hξ : ClassicalDetects (background.classicalConvergence X) (s+q+1,t+q) x ξ) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q)-(s+q+1)))≫ξ≫f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal⟩ := prescribed_native_source hcomp X (s+q+1) (t+q) x ξ hx hξ
  have hfirst : (c≫background.nu.functor.map f)≫XModLambdaN.incl _ 1=
      nativeFirstLabel Y (s+q+1) (t+q) ((background.classical.map f).pageMap 2 _ x) := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hc,native_first_label_natural]
  have hzero : (c≫background.nu.functor.map f)≫background.nu.functor.map g=0 := by
    rw [Category.assoc,hfg,comp_zero]
  obtain ⟨hvp,hvd⟩ := ordinary_boundary_lift_full_image R hcomp Y Z g q hq s t a _ v
    hd hd' (c≫background.nu.functor.map f) hfirst hzero P hP hvP hkernel
  have hreal' : (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
      background.recovery.realization.map (c≫background.nu.functor.map f)≫(hcomp.nu Y).target.hom=ξ≫f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target X]
    simpa only [Category.assoc] using congrArg (fun z => z≫f) hreal
  exact ⟨hvp,by simpa only [hreal'] using hvd⟩

public def boundaryLabelRegrade {X : (AdamsObject (coefficients := background.coefficients))} {s t s' t' : ℤ}
    (hs : s=s') (ht : t=t') (x : Ambient background X (s,t)) : Ambient background X (s',t') :=
  (show (s,t)=(s',t') from Prod.ext hs ht) ▸ x

private theorem boundary_label_regrade_native {X : (AdamsObject (coefficients := background.coefficients))} {s t s' t' : ℤ}
    (hs : s=s') (ht : t=t') (x : Ambient background X (s,t)) :
    nativeFirstLabel X s' t' (boundaryLabelRegrade hs ht x)=
      homotopyRegrade (by omega) ht (nativeFirstLabel X s t x) := by
  subst s'; subst t'; rfl

/-- Positive first normalization and ordinary second map. Vertical
translation preserves the source realization; the positive first operation
is the prescribed d_(q+1) target. The first/second composite is zero. -/
private theorem positive_first_boundary_lift_prescribed_source
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hfg : normalizedFirstMap T hf≫background.nu.functor.map T.g=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s+q,t+q-1))
    (a : Ambient background T.Y (s,t))
    (v : Ambient background T.Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a
      (boundaryLabelRegrade rfl (by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q-1) x)))
    (hd' : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((q+1)+1) (s,t) (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))
      ((background.classical.map T.g).pageMap 2 (s,t) a)
      ((background.classical.map T.g).pageMap 2 _ v))
    (P : Submodule ℤ (Ambient background T.Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background T.Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → (background.classical.map T.g).pageMap 2 _ z ∈
      boundaries background T.Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) _ z)
    (ξ : HomotopyGroup ((t+q-1)-(s+q)) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s+q,t+q-1) x)
    (hξ : ClassicalDetects (background.classicalConvergence T.X) (s+q,t+q-1) x ξ) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence T.Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q-1)-(s+q)))≫ξ≫T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal⟩ := prescribed_native_source hcomp T.X (s+q) (t+q-1) x ξ hx hξ
  let c' := verticalTranslate _ 1 ((t+q-1)-(s+q)) (t+q-1) c
  have hc' := positive_full_source_first_label T.X (s+q) (t+q-1) x c hc
  let image : BiHom ((t+q)-(s+q+1)) (t+q)
      (background.nu.functor.obj (T.Y.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) (c'≫normalizedFirstMap T hf)
  have hfirst : image≫XModLambdaN.incl _ 1=nativeFirstLabel T.Y (s+q+1) (t+q)
      (boundaryLabelRegrade rfl (by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q-1) x)) := by
    rw [boundary_label_regrade_native,cofiberFirstQuotientBoundary_native_label,
      normalized_homotopy_regrade_trans]
    dsimp only [image]
    rw [←regrade_comp,Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hc']
  have hzero : image≫background.nu.functor.map T.g=0 := by
    dsimp only [image]
    rw [←regrade_comp,Category.assoc,hfg,comp_zero]
    exact regrade_zero _ _
  obtain ⟨hvp,hvd⟩ := ordinary_boundary_lift_full_image R hcomp T.Y T.Z T.g q hq s t a _ v
    hd hd' image hfirst hzero P hP hvP hkernel
  have hrealc : (R.sphere ((t+q-1)-(s+q)) ((t+q-1)+1)).hom≫
      background.recovery.realization.map c'≫(hcomp.shiftedNu T.X 1).target.hom=ξ :=
    (positive_source_realization_eq R hcomp T.X 1 _ _ c).trans hreal
  have hraw : (R.sphere ((t+q-1)-(s+q)) ((t+q-1)+1)).hom≫
      background.recovery.realization.map (c'≫normalizedFirstMap T hf)≫(hcomp.nu T.Y).target.hom=ξ≫T.f := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [normalized_positive_realization_square R hcomp T hf]
    simpa only [Category.assoc] using congrArg (fun e => e≫T.f) hrealc
  have hri := realization_homotopy_regrade_full R
    (by omega : (t+q-1)-(s+q)=(t+q)-(s+q+1))
    (by omega : (t+q-1)+1=t+q) (c'≫normalizedFirstMap T hf)
  have hri' := congrArg (fun e => e≫(hcomp.nu T.Y).target.hom) hri
  simp only [Category.assoc] at hri'
  rw [hraw] at hri'
  have hi : (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
      background.recovery.realization.map image≫(hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
        (t+q)-(s+q+1)=(t+q-1)-(s+q)))≫ξ≫T.f := hri'
  rw [hi] at hvd
  refine ⟨hvp,?_⟩
  simpa only [←Category.assoc,eqToHom_trans] using hvd

private theorem lambda_torsion_precomp_sphere_iso {A : SyntheticSpectrum}
    (m w : ℤ) (k : ℕ) (a : BiHom m w A)
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w)
    (ha : lambdaMultiply k a=0) : lambdaMultiply k (u.hom≫a)=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi] at ha ⊢
  rw [←Category.assoc,←lambdaPow_naturality,Category.assoc,ha,comp_zero]

/-- The torsion correction retains the coordinate automorphism
of the selected quotient-shift comparison, which fixes the first label. -/
private def positiveAdjustedBoundary (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
  homotopyRegrade (by omega) rfl
    ((positiveBoundarySourceIso 1 q (t-s) t).hom≫
      biSuspensionHomEquiv (t-s) t q (background.nu.functor.obj (Y.obj background.auxiliary))
        (z≫XModLambdaN.proj _ q))

private theorem positive_adjusted_boundary_first (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    positiveAdjustedBoundary Y q s t z≫XModLambdaN.incl _ 1=
      boundaryRepresentative Y q s t z≫XModLambdaN.incl _ 1 := by
  simp only [positiveAdjustedBoundary,boundaryRepresentative,←regrade_comp,Category.assoc,
    sphere_automorphism_quotient_projection]

private theorem positive_adjusted_boundary_torsion (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    lambdaMultiply q (positiveAdjustedBoundary Y q s t z)=0 := by
  dsimp only [positiveAdjustedBoundary]
  rw [lambda_regrade,lambda_torsion_precomp_sphere_iso _ _ q _ _
    (absolute_boundary_lambda_zero _ _ _ _ z)]
  exact regrade_zero _ _

private theorem vertical_translate_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (e : ℤ) (a : BiHom m w A) :
    verticalTranslate A e m' w' (homotopyRegrade hm hw a)=
      homotopyRegrade hm (congrArg (fun z => z+e) hw) (verticalTranslate A e m w a) := by
  subst m'; subst w'; rfl

private theorem positive_adjusted_boundary_shift (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q) (positiveAdjustedBoundary Y q s t z)=
      homotopyRegrade (by omega) (by omega)
        (biSuspensionHomEquiv (t-s) (t+1) q
          ((SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)))
          ((verticalTranslate _ 1 (t-s) t z≫(levelQuotientShiftIso Y 1 q).inv)≫
            XModLambdaN.proj _ q)) := by
  dsimp only [positiveAdjustedBoundary]
  rw [vertical_translate_regrade,shifted_absolute_boundary_eq_precomp,
    normalized_homotopy_regrade_trans]

private theorem bi_susp_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (q : ℕ)
    (a : BiHom m w (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧)) :
    biSuspensionHomEquiv m' w' q A (homotopyRegrade hm hw a)=
      homotopyRegrade (by omega) (by omega) (biSuspensionHomEquiv m w q A a) := by
  subst m'; subst w'; rfl

private def positiveBoundaryFiniteImage (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    BiHom ((t+1)-(s+1)) (t+1) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) q) :=
  homotopyRegrade (by omega) rfl
    (verticalTranslate _ 1 (t-s) t z≫(levelQuotientShiftIso Y 1 q).inv≫XModLambdaN.map G q)

private theorem positive_boundary_finite_image_boundary (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    boundaryRepresentative Z q (s+1) (t+1) (positiveBoundaryFiniteImage Y Z G q s t z)=
      homotopyRegrade (by omega) (by omega)
        (verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q) (positiveAdjustedBoundary Y q s t z)≫G) := by
  rw [positive_adjusted_boundary_shift,regrade_comp,normalized_homotopy_regrade_trans]
  dsimp only [boundaryRepresentative,positiveBoundaryFiniteImage]
  rw [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans]
  rw [Category.assoc,Category.assoc,XModLambdaN.proj_naturality]
  rw [←Category.assoc,←Category.assoc,bi_susp_natural background.quotients.coherence,regrade_comp]

private theorem positive_boundary_finite_image_first (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (a : Ambient background Y (s,t))
    (ha : z≫(background.quotients.tower _).rho 1 q hq=nativeFirstLabel Y s t a) :
    positiveBoundaryFiniteImage Y Z G q s t z≫(background.quotients.tower _).rho 1 q hq=
      nativeFirstLabel Z (s+1) (t+1) (positiveFirstQuotientOperation Y Z G s t a) := by
  have hsource : (verticalTranslate _ 1 (t-s) t z≫(levelQuotientShiftIso Y 1 q).inv)≫
      (background.quotients.tower _).rho 1 q hq=(background.firstQuotient Y 1 s t).symm a := by
    apply (cancel_mono (levelQuotientShiftIso Y 1 1).hom).mp
    rw [Category.assoc,quotient_shift_restriction_on_spheres Y (0,1) 1 q
      (by decide) hq (levelQuotientShiftIso Y 1 1) (levelQuotientShiftIso Y 1 q)
      (level_quotient_shift_incl Y 1 1) (level_quotient_shift_incl Y 1 q)]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    rw [vertical_translate_comp,ha,←positive_first_label_shift Y s t a]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  dsimp only [positiveBoundaryFiniteImage]
  rw [←regrade_comp]
  simp only [Category.assoc]
  rw [←(background.quotients.natural G).rho_naturality]
  simp only [←Category.assoc]
  rw [hsource,positive_first_quotient_native_label]

private theorem positive_adjusted_differential_correction
    (R : RealizationCoordinates background) (Y : (AdamsObject (coefficients := background.coefficients)))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : Ambient background Y (s,t)) (y : Ambient background Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a y)
    (image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (himage : image≫XModLambdaN.incl _ 1=nativeFirstLabel Y (s+q+1) (t+q) y) :
    ∃ z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q),
      z≫(background.quotients.tower _).rho 1 q hq=nativeFirstLabel Y s t a ∧
      ∃ b : BiHom ((t+q)-(s+q+1)) (t+q+1) (background.nu.functor.obj (Y.obj background.auxiliary)),
        homotopyRegrade rfl (by omega) (lambdaMultiply 1 b)=image-positiveAdjustedBoundary Y q s t z ∧
        (R.sphere ((t+q)-(s+q+1)) (t+q+1)).hom≫background.recovery.realization.map b=
          (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫background.recovery.realization.map image := by
  obtain ⟨z,hz,hzy⟩ := (differential_iff_specified_adjacent_lift Y q hq s t a y).mp hd
  change boundaryRepresentative Y q s t z≫XModLambdaN.incl _ 1=
    nativeFirstLabel Y (s+q+1) (t+q) y at hzy
  let im : BiHom ((t+q)-(s+q+1)) ((t+q+1)-1) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade rfl (by omega) image
  let τ : BiHom ((t+q)-(s+q+1)) ((t+q+1)-1) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade rfl (by omega) (positiveAdjustedBoundary Y q s t z)
  have hfirst : im≫XModLambdaN.incl _ 1=τ≫XModLambdaN.incl _ 1 := by
    dsimp only [im,τ]
    rw [←regrade_comp,←regrade_comp,positive_adjusted_boundary_first,himage,hzy]
  have hτ : lambdaMultiply q τ=0 := by
    dsimp only [τ]
    rw [lambda_regrade,positive_adjusted_boundary_torsion]
    exact regrade_zero _ _
  obtain ⟨b,hb,hreal⟩ := torsion_corrected_full_image R Y _ (t+q+1) q im τ hfirst hτ
  refine ⟨z,hz,b,?_,?_⟩
  · rw [hb]
    simp only [im,τ,regrade_precomp,Preadditive.comp_sub,←Category.assoc,
      eqToHom_trans,eqToHom_refl,Category.id_comp]
  · rw [hreal]
    have hh := realization_homotopy_regrade_full R rfl (by omega : t+q=(t+q+1)-1) image
    simpa only [im,eqToHom_refl,Category.id_comp] using hh

private theorem positive_lambda_correction {A B : SyntheticSpectrum}
    (G : (SyntheticCategory.biShift (0,1)).obj A ⟶ B)
    (m w : ℤ) (image τ : BiHom m w A) (b : BiHom m (w+1) A)
    (hc : homotopyRegrade rfl (by omega) (lambdaMultiply 1 b)=image-τ)
    (hz : verticalTranslate A 1 m w image≫G=0) :
    homotopyRegrade rfl (by omega)
      (lambdaMultiply 1 (verticalTranslate A 1 m (w+1) b≫G))=
        -(verticalTranslate A 1 m w τ≫G) := by
  have hh := congrArg (fun z => verticalTranslate A 1 m w z≫G) hc
  rw [map_sub,Preadditive.sub_comp,hz,zero_sub] at hh
  rw [vertical_translate_regrade,←lambda_multiply_vertical_translate_comm A 1 1 m (w+1) b,
    normalized_homotopy_regrade_trans,←regrade_comp] at hh
  simpa only [lambdaMultiply,Category.assoc] using hh

private theorem positive_mapped_correction_adjacent_lift
    (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (b : BiHom ((t+q)-(s+q+1)) (t+q+1) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hc : homotopyRegrade rfl (by omega) (lambdaMultiply 1 b)=image-positiveAdjustedBoundary Y q s t z)
    (hz : verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q) image≫G=0) :
    let bZ : BiHom (((t+1)+((q+1:ℕ):ℤ))-((s+1)+((q+1:ℕ):ℤ)+1)) ((t+1)+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Z.obj background.auxiliary)) :=
      homotopyRegrade (by omega) (by omega)
        (verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q+1) b≫G)
    ∃ eta : BiHom ((t+1)-(s+1)) (t+1) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) (q+1)),
      eta≫(background.quotients.tower _).rho 1 (q+1) (by omega)=
        positiveBoundaryFiniteImage Y Z G q s t z≫(background.quotients.tower _).rho 1 q hq ∧
      lambdaMultiply 1 (bZ+boundaryRepresentative Z (q+1) (s+1) (t+1) eta)=0 := by
  dsimp only
  let zZ := positiveBoundaryFiniteImage Y Z G q s t z
  let bZ : BiHom (((t+1)+((q+1:ℕ):ℤ))-((s+1)+((q+1:ℕ):ℤ)+1)) ((t+1)+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Z.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega)
      (verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q+1) b≫G)
  have heq : homotopyRegrade (by omega) (by omega) (lambdaMultiply 1 bZ)=
      (0 : BiHom (((t+1)+q)-((s+1)+q+1)) ((t+1)+q) _)-
        boundaryRepresentative Z q (s+1) (t+1) zZ := by
    have h := positive_lambda_correction G _ _ image (positiveAdjustedBoundary Y q s t z) b hc hz
    have hh := congrArg (homotopyRegrade (by omega :
      (t+q)-(s+q+1)=((t+1)+q)-((s+1)+q+1)) (by omega : (t+q)+1=(t+1)+q)) h
    dsimp only [bZ,zZ]
    rw [lambda_regrade,normalized_homotopy_regrade_trans,zero_sub,
      positive_boundary_finite_image_boundary]
    simpa only [normalized_homotopy_regrade_trans,regrade_precomp,Preadditive.comp_neg,
      ←Category.assoc,eqToHom_trans] using hh
  have hfirst : (0 : BiHom (((t+1)+q)-((s+1)+q+1)) ((t+1)+q) _)≫XModLambdaN.incl _ 1=
      boundaryRepresentative Z q (s+1) (t+1) zZ≫XModLambdaN.incl _ 1 := by
    have hh := congrArg (fun e => e≫XModLambdaN.incl _ 1) heq
    rw [←regrade_comp,lambdaMultiply_quotient_zero,regrade_zero,
      zero_sub,Preadditive.neg_comp] at hh
    rw [zero_comp]
    exact (neg_eq_zero.mp hh.symm).symm
  obtain ⟨eta,_,he,herr⟩ := mapped_correction_adjacent_lift Z Z (𝟙 _) q hq (s+1) (t+1)
    zZ 0 bZ hfirst (by simp) heq
  exact ⟨eta,by simpa only [background.quotients.functoriality.map_id,Category.comp_id] using he,
    by simpa only [Category.comp_id] using herr⟩

private def positiveBoundaryTargetOperation (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ) (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))) :
    Ambient background Z ((s+1)+((q+1:ℕ):ℤ)+1,(t+1)+((q+1:ℕ):ℤ)) :=
  boundaryLabelRegrade (by omega) (by omega)
    (positiveFirstQuotientOperation Y Z G _ _ v)

private theorem boundary_label_regrade_sub {X : (AdamsObject (coefficients := background.coefficients))} {s t s' t' : ℤ}
    (hs : s=s') (ht : t=t') (x y : Ambient background X (s,t)) :
    boundaryLabelRegrade hs ht (x-y)=boundaryLabelRegrade hs ht x-boundaryLabelRegrade hs ht y := by
  subst s'; subst t'; rfl

private theorem positive_boundary_target_sub (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ) (v w : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))) :
    positiveBoundaryTargetOperation Y Z G q s t (v-w)=
      positiveBoundaryTargetOperation Y Z G q s t v-positiveBoundaryTargetOperation Y Z G q s t w := by
  simp only [positiveBoundaryTargetOperation,positiveFirstQuotientOperation,map_sub,
    Preadditive.sub_comp,regrade_precomp,Preadditive.comp_sub,boundary_label_regrade_sub]

/-- Full-image absolute-boundary permanence for a positive second map.
The first differential constructs a coordinate-corrected torsion class
with zero realization, so the final detector preserves the given full image. -/
private theorem positive_second_boundary_lift_full_image
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (Y Z : (AdamsObject (coefficients := background.coefficients)))
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : Ambient background Y (s,t)) (y : Ambient background Y (s+q+1,t+q))
    (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a y)
    (hd' : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      ((q+1)+1) (s+1,t+1) ((s+1)+((q+1:ℕ):ℤ)+1,(t+1)+((q+1:ℕ):ℤ))
      (positiveFirstQuotientOperation Y Z G s t a)
      (positiveBoundaryTargetOperation Y Z G q s t v))
    (image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (himage : image≫XModLambdaN.incl _ 1=nativeFirstLabel Y (s+q+1) (t+q) y)
    (hzero : verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q) image≫G=0)
    (P : Submodule ℤ (Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → positiveBoundaryTargetOperation Y Z G q s t z ∈
      boundaries background Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ z) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q)-(s+q+1)))≫
          (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
            background.recovery.realization.map image≫(hcomp.nu Y).target.hom) := by
  obtain ⟨z,hz,b,hb,hreal⟩ := positive_adjusted_differential_correction R Y q hq s t a y hd image himage
  obtain ⟨eta,heta,herr⟩ := positive_mapped_correction_adjacent_lift Y Z G q hq s t z image b hb hzero
  have heta' : eta≫(background.quotients.tower _).rho 1 (q+1) (by omega)=
      nativeFirstLabel Z (s+1) (t+1) (positiveFirstQuotientOperation Y Z G s t a) :=
    heta.trans (positive_boundary_finite_image_first Y Z G q hq s t z a hz)
  let b' : BiHom ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)) (t+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Y.obj background.auxiliary)) := homotopyRegrade (by omega) (by omega) b
  let bZ : BiHom (((t+1)+((q+1:ℕ):ℤ))-((s+1)+((q+1:ℕ):ℤ)+1)) ((t+1)+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Z.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega)
      (verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q+1) b≫G)
  obtain ⟨w,hw,hwp,hwd⟩ := full_representative_first_label_detects R hcomp Y
    (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) b'
  have hbG : bZ≫XModLambdaN.incl _ 1=nativeFirstLabel Z _ _
      (positiveBoundaryTargetOperation Y Z G q s t w) := by
    have h := positive_full_source_first_label Y (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) w b' hw
    have hh := congrArg (fun u => u≫XModLambdaN.map G 1) h
    simp only [Category.assoc,←XModLambdaN.incl_naturality] at hh
    rw [positiveBoundaryTargetOperation,boundary_label_regrade_native,
      positive_first_quotient_native_label,←hh]
    simp only [bZ,b',vertical_translate_regrade,normalized_homotopy_regrade_trans,regrade_comp,Category.assoc]
  have hdiff := adjacent_lambda_error_is_boundary Z q hq (s+1) (t+1) _ _ _ eta heta' bZ hbG herr hd'
  have hfinal : IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ (w-v) :=
    hkernel (w-v) (P.sub_mem (hP hwp) hvP) (by
      simpa only [positive_boundary_target_sub] using hdiff)
  have htransport := realization_homotopy_regrade_full R
    (by omega : (t+q)-(s+q+1)=(t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1))
    (by omega : t+q+1=t+((q+1:ℕ):ℤ)) b
  rw [hreal] at htransport
  have htransport' := congrArg (fun e => e≫(hcomp.nu Y).target.hom) htransport
  simp only [Category.assoc] at htransport'
  have hdet := htransport' ▸ hwd
  exact classical_detects_of_final_boundary_difference Y _ w v _ hdet hfinal

/-- Ordinary first and positive second normalization: every prescribed strict source retains its exact image. -/
private theorem ordinary_first_positive_second_boundary_lift_prescribed_source
    (X Y Z : (AdamsObject (coefficients := background.coefficients)))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (hfg : (SyntheticCategory.biShift (0,1)).map (background.nu.functor.map f)≫G=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background X (s+q+1,t+q))
    (a : Ambient background Y (s,t))
    (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a ((background.classical.map f).pageMap 2 _ x))
    (hd' : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      ((q+1)+1) (s+1,t+1) ((s+1)+((q+1:ℕ):ℤ)+1,(t+1)+((q+1:ℕ):ℤ))
      (positiveFirstQuotientOperation Y Z G s t a)
      (positiveBoundaryTargetOperation Y Z G q s t v))
    (P : Submodule ℤ (Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → positiveBoundaryTargetOperation Y Z G q s t z ∈
      boundaries background Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ z)
    (ξ : HomotopyGroup ((t+q)-(s+q+1)) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s+q+1,t+q) x)
    (hξ : ClassicalDetects (background.classicalConvergence X) (s+q+1,t+q) x ξ) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q)-(s+q+1)))≫ξ≫f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal⟩ := prescribed_native_source hcomp X (s+q+1) (t+q) x ξ hx hξ
  have hfirst : (c≫background.nu.functor.map f)≫XModLambdaN.incl _ 1=
      nativeFirstLabel Y (s+q+1) (t+q) ((background.classical.map f).pageMap 2 _ x) := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hc,native_first_label_natural]
  have hzero : verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q) (c≫background.nu.functor.map f)≫G=0 := by
    rw [←vertical_translate_comp,Category.assoc,hfg,comp_zero]
  obtain ⟨hvp,hvd⟩ := positive_second_boundary_lift_full_image R hcomp Y Z G q hq s t a _ v
    hd hd' (c≫background.nu.functor.map f) hfirst hzero P hP hvP hkernel
  have hreal' : (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
      background.recovery.realization.map (c≫background.nu.functor.map f)≫(hcomp.nu Y).target.hom=ξ≫f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target X]
    simpa only [Category.assoc] using congrArg (fun z => z≫f) hreal
  exact ⟨hvp,by simpa only [hreal'] using hvd⟩


/-- Absolute-boundary permanence for positive first and second operations
on the normalized pair. -/
private theorem positive_pair_boundary_lift_prescribed_source
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (G : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (T.Z.obj background.auxiliary))
    (hfg : (SyntheticCategory.biShift (0,1)).map (normalizedFirstMap T hf)≫G=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s+q,t+q-1))
    (a : Ambient background T.Y (s,t))
    (v : Ambient background T.Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a
      (boundaryLabelRegrade rfl (by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q-1) x)))
    (hd' : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((q+1)+1) (s+1,t+1) ((s+1)+((q+1:ℕ):ℤ)+1,(t+1)+((q+1:ℕ):ℤ))
      (positiveFirstQuotientOperation T.Y T.Z G s t a)
      (positiveBoundaryTargetOperation T.Y T.Z G q s t v))
    (P : Submodule ℤ (Ambient background T.Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background T.Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → positiveBoundaryTargetOperation T.Y T.Z G q s t z ∈
      boundaries background T.Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) _ z)
    (ξ : HomotopyGroup ((t+q-1)-(s+q)) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s+q,t+q-1) x)
    (hξ : ClassicalDetects (background.classicalConvergence T.X) (s+q,t+q-1) x ξ) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence T.Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q-1)-(s+q)))≫ξ≫T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal⟩ := prescribed_native_source hcomp T.X (s+q) (t+q-1) x ξ hx hξ
  let c' := verticalTranslate _ 1 ((t+q-1)-(s+q)) (t+q-1) c
  have hc' := positive_full_source_first_label T.X (s+q) (t+q-1) x c hc
  let image : BiHom ((t+q)-(s+q+1)) (t+q)
      (background.nu.functor.obj (T.Y.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) (c'≫normalizedFirstMap T hf)
  have hfirst : image≫XModLambdaN.incl _ 1=nativeFirstLabel T.Y (s+q+1) (t+q)
      (boundaryLabelRegrade rfl (by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q-1) x)) := by
    rw [boundary_label_regrade_native,cofiberFirstQuotientBoundary_native_label,
      normalized_homotopy_regrade_trans]
    dsimp only [image]
    rw [←regrade_comp,Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hc']
  have hzero : verticalTranslate _ 1 ((t+q)-(s+q+1)) (t+q) image≫G=0 := by
    dsimp only [image]
    rw [vertical_translate_regrade,←regrade_comp,←vertical_translate_comp,Category.assoc,hfg,comp_zero]
    exact regrade_zero _ _
  obtain ⟨hvp,hvd⟩ := positive_second_boundary_lift_full_image R hcomp T.Y T.Z G q hq s t a _ v
    hd hd' image hfirst hzero P hP hvP hkernel
  have hrealc : (R.sphere ((t+q-1)-(s+q)) ((t+q-1)+1)).hom≫
      background.recovery.realization.map c'≫(hcomp.shiftedNu T.X 1).target.hom=ξ :=
    (positive_source_realization_eq R hcomp T.X 1 _ _ c).trans hreal
  have hraw : (R.sphere ((t+q-1)-(s+q)) ((t+q-1)+1)).hom≫
      background.recovery.realization.map (c'≫normalizedFirstMap T hf)≫(hcomp.nu T.Y).target.hom=ξ≫T.f := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [normalized_positive_realization_square R hcomp T hf]
    simpa only [Category.assoc] using congrArg (fun e => e≫T.f) hrealc
  have hri := realization_homotopy_regrade_full R
    (by omega : (t+q-1)-(s+q)=(t+q)-(s+q+1))
    (by omega : (t+q-1)+1=t+q) (c'≫normalizedFirstMap T hf)
  have hri' := congrArg (fun e => e≫(hcomp.nu T.Y).target.hom) hri
  simp only [Category.assoc] at hri'
  rw [hraw] at hri'
  have hi : (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
      background.recovery.realization.map image≫(hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
        (t+q)-(s+q+1)=(t+q-1)-(s+q)))≫ξ≫T.f := hri'
  rw [hi] at hvd
  refine ⟨hvp,?_⟩
  simpa only [←Category.assoc,eqToHom_trans] using hvd


end
end KIP126.ProofTools.Internal.SyntheticCoverage
