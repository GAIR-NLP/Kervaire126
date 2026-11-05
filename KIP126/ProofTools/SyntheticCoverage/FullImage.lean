module

import all KIP126.ProofTools.FiniteLifting.LevelSourceLift
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein

/-! A zero first quotient of the specified full image gives
a lambda preimage whose permanent first label detects
the realization of that image. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

/-- Exactness of the lambda cofiber gives a preimage of the specified image. -/
private theorem full_image_lambda_preimage
    {A B : SyntheticSpectrum} (g : A ⟶ B) (m w : ℤ)
    (a : BiHom m w A) (hz : (a ≫ g) ≫ XModLambdaN.incl B 1 = 0) :
    ∃ b : BiHom m w ((SyntheticCategory.biShift (0,-(1:ℤ))).obj B),
      b ≫ lambdaPow 1 B = a ≫ g := by
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle B 1).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished B 1) (a ≫ g) hz
  exact ⟨b,hb.symm⟩

/-- The same exactness statement in native unshifted homotopy degrees. -/
private theorem full_image_lambda_preimage_native
    {A B : SyntheticSpectrum} (g : A ⟶ B) (m t : ℤ)
    (a : BiHom m (t-1) A) (hz : (a ≫ g) ≫ XModLambdaN.incl B 1 = 0) :
    ∃ b : BiHom m t B, lambdaMultiply 1 b = a ≫ g := by
  obtain ⟨b₀,hb₀⟩ := full_image_lambda_preimage g m (t-1) a hz
  let δ : ℤ × ℤ := (0,-1)
  let p : ℤ × ℤ := (m,t)
  let b₁ : BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj B) :=
    homotopyRegrade (by simp [p,δ]) (by dsimp [p,δ]; omega) b₀
  let b : BiHom m t B := (SyntheticCategory.biShift_fullyFaithful δ).preimage
    ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ b₁)
  have hb : shiftHomotopyClass δ p b = b₁ := by
    simp [b,shiftHomotopyClass]
  refine ⟨b,?_⟩
  rw [lambda_multiply_raw m t 1 b]
  rw [show shiftHomotopyClass (0,-((1:ℕ):ℤ)) (m,t) b = b₁ from hb]
  dsimp only [b₁]
  rw [regrade_comp,normalized_homotopy_regrade_trans]
  simpa only [homotopyRegrade] using hb₀

private theorem native_first_label_surjective (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ) :
    Function.Surjective (nativeFirstLabel X s t) := by
  intro a
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  obtain ⟨x,hx⟩ := firstLabel_surjective X s t
    (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app V) 1)
  refine ⟨x,?_⟩
  unfold nativeFirstLabel
  rw [hx,Category.assoc,←background.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app,background.quotients.functoriality.map_id]
  simp only [Functor.id_obj,V,Category.comp_id]

/-- A native full representative supplies its own permanent first label
and detection of its specified realization, including a zero final class. -/
private theorem full_representative_first_label_detects
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (Y : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (b : BiHom (t-s) t (background.nu.functor.obj (Y.obj background.auxiliary))) :
    ∃ w : Ambient background Y (s,t),
      b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y s t w ∧
      w ∈ permanentCycles background Y (s,t) ∧
      ClassicalDetects (background.classicalConvergence Y) (s,t) w
        ((R.sphere (t-s) t).hom ≫ background.recovery.realization.map b ≫
          (hcomp.nu Y).target.hom) := by
  obtain ⟨w,hw⟩ := native_first_label_surjective Y s t (b ≫ XModLambdaN.incl _ 1)
  have hlabel := hw.symm
  have hp := first_label_lift_permanent Y s t w b hlabel
  have hdet := nu_first_label_detects Y s t w hp b hlabel
  have hc := (hcomp.nu Y).detects s t t _ b hdet
  dsimp only [nuWeightLabel] at hc
  rw [KIP126.ProofTools.Paper.paper_e2Map_regrade background _ s t _ t
    (show t-((t-t).toNat:ℤ)=t by simp),hcomp.nu_e2] at hc
  exact ⟨w,hlabel,hp,hc⟩

/-- If this full image vanishes in the first quotient, its actual lambda
preimage provides a permanent label detecting the realization of that same
image. This is the full-image step, before the candidate/kernel comparison. -/
private theorem full_image_first_label_detects
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (A : SyntheticSpectrum) (Y : (AdamsObject (coefficients := background.coefficients)))
    (g : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary)) (s t : ℤ)
    (a : BiHom (t-s) (t-1) A)
    (hz : (a ≫ g) ≫ XModLambdaN.incl _ 1 = 0) :
    ∃ b : BiHom (t-s) t (background.nu.functor.obj (Y.obj background.auxiliary)),
      lambdaMultiply 1 b = a ≫ g ∧
      ∃ w : Ambient background Y (s,t),
        b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y s t w ∧
        w ∈ permanentCycles background Y (s,t) ∧
        ClassicalDetects (background.classicalConvergence Y) (s,t) w
          ((R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a ≫ g) ≫
            (hcomp.nu Y).target.hom) := by
  obtain ⟨b,hb⟩ := full_image_lambda_preimage_native g (t-s) t a hz
  obtain ⟨w,hw,hp,hclass⟩ := full_representative_first_label_detects R hcomp Y s t b
  refine ⟨b,hb,w,hw,hp,?_⟩
  have he := realization_lambda_multiply R (t-s) t 1 b
  rw [hb] at he
  have he' : (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a ≫ g) ≫
      (hcomp.nu Y).target.hom =
      (R.sphere (t-s) t).hom ≫ background.recovery.realization.map b ≫
        (hcomp.nu Y).target.hom := by
    convert congrArg (fun u => u ≫ (hcomp.nu Y).target.hom) he using 1 <;>
      simp only [Category.assoc]
    rfl
  exact he'.symm ▸ hclass

/-- For the normalized classical map, the permanent label obtained
by dividing its full image detects the image of the specified
full source realization. -/
private theorem normalized_full_image_first_label_detects
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ)
    (a : BiHom (t-s) (t-1)
      ((SyntheticCategory.biShift (0,(normalizedExponent background.classicalTower f:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary))))
    (hz : (a ≫ (background.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ 1 = 0) :
    ∃ b : BiHom (t-s) t (background.nu.functor.obj (Y.obj background.auxiliary)),
      lambdaMultiply 1 b = a ≫ (background.normalizedMap X Y f).map ∧
      ∃ w : Ambient background Y (s,t),
        b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y s t w ∧
        w ∈ permanentCycles background Y (s,t) ∧
        ClassicalDetects (background.classicalConvergence Y) (s,t) w
          (((R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map a ≫
            (hcomp.shiftedNu X (normalizedExponent background.classicalTower f)).target.hom) ≫ f) := by
  obtain ⟨b,hb,w,hw,hp,hclass⟩ := full_image_first_label_detects R hcomp _ Y
    (background.normalizedMap X Y f).map s t a hz
  refine ⟨b,hb,w,hw,hp,?_⟩
  have he : (R.sphere (t-s) (t-1)).hom ≫
      background.recovery.realization.map (a ≫ (background.normalizedMap X Y f).map) ≫
        (hcomp.nu Y).target.hom =
      ((R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map a ≫
        (hcomp.shiftedNu X (normalizedExponent background.classicalTower f)).target.hom) ≫ f := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [KIP126.ProofTools.Paper.normalized_realization_square background R hcomp X Y f]
  exact he ▸ hclass

end
end KIP126.ProofTools.Internal.SyntheticCoverage
