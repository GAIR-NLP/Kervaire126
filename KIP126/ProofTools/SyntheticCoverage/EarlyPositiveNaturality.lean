module

import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.LastLayerNative
import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource

/-! Actual coefficient division and positive normalized images.

The selected finite coefficient triangle supplies a native preimage of a
specified class with zero restriction. The actual positive normalized map
commutes with that coefficient insertion, using the chosen quotient shift
comparisons and their inclusion compatibility.
-/

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
set_option maxHeartbeats 3000000

private theorem early_coefficient_shift_regrade (A : SyntheticSpectrum)
    (N i : ℕ) (hiN : i < N) {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (b : BiHom m w (XModLambdaN A (N-i))) :
    homotopyRegrade hm (congrArg (fun v : ℤ => v-i) hw)
        (finiteCoefficientShiftClass A N i hiN m w b) =
      finiteCoefficientShiftClass A N i hiN m' w' (homotopyRegrade hm hw b) := by
  subst m'; subst w'; rfl

/-- The normalized finite image commutes with the actual lambda insertion.
The comparisons at both lengths are retained as specified inputs. -/
private theorem positive_finite_image_coefficient_shift
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N i : ℕ) (hiN : i < N) (m w : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (N-i) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (N-i)))
    (εN : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hεn : XModLambdaN.incl _ (N-i) ≫ εn.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (N-i)))
    (hεN : XModLambdaN.incl _ N ≫ εN.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (b : BiHom m w
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (N-i))) :
    positiveFiniteImage T hf N εN m (w-i)
        (finiteCoefficientShiftClass _ N i hiN m w b) =
      homotopyRegrade rfl (show (w+1)-i=(w-i)+1 by omega)
        (finiteCoefficientShiftClass _ N i hiN m (w+1)
          (positiveFiniteImage T hf (N-i) εn m w b)) := by
  have h := finite_coefficient_shift_bigraded_all T.X (0,1) N i hiN m w
    εn εN hεn hεN b
  have hh := congrArg (fun z => z ≫ XModLambdaN.map (lastLayerNormalizedMap T hf) N) h
  rw [finite_coefficient_shift_natural] at hh
  have hhm := congrArg (homotopyRegrade (show m+0=m by omega)
    (rfl : w+1-i=w+1-i)) hh
  rw [early_coefficient_shift_regrade] at hhm
  have hh' := congrArg (homotopyRegrade (rfl : m=m)
    (show w+1-i=(w-i)+1 by omega)) hhm
  simpa only [positiveFiniteImage, regrade_comp, last_layer_regrade_trans,
    early_coefficient_shift_regrade, Category.assoc] using hh'

/-- Canonical level comparisons specialize the preceding naturality square. -/
private theorem positive_finite_image_coefficient_shift_level
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N i : ℕ) (hiN : i < N) (m w : ℤ)
    (b : BiHom m w
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (N-i))) :
    positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m (w-i)
        (finiteCoefficientShiftClass _ N i hiN m w b) =
      homotopyRegrade rfl (show (w+1)-i=(w-i)+1 by omega)
        (finiteCoefficientShiftClass _ N i hiN m (w+1)
          (positiveFiniteImage T hf (N-i)
            (levelQuotientShiftIso T.X 1 (N-i)) m w b)) :=
  positive_finite_image_coefficient_shift T hf N i hiN m w
    (levelQuotientShiftIso T.X 1 (N-i)) (levelQuotientShiftIso T.X 1 N)
    (level_quotient_shift_incl T.X 1 (N-i)) (level_quotient_shift_incl T.X 1 N) b

/-- Zero restriction gives a native preimage under the actual coefficient
insertion; the output is constructed by triangle exactness. -/
private theorem native_coefficient_preimage_of_zero_restriction
    (A : SyntheticSpectrum) (N i : ℕ) (hi : 0 < i) (hiN : i < N)
    (m w : ℤ) (a : BiHom m (w-i) (XModLambdaN A N))
    (ha : a ≫ (background.quotients.tower A).rho i N hiN.le = 0) :
    ∃ b : BiHom m w (XModLambdaN A (N-i)),
      finiteCoefficientShiftClass A N i hiN m w b = a := by
  let C := (background.quotients.tower A).triangle hi hiN
  have hz : a ≫ C.rho = 0 := by
    simpa only [C,(background.quotients.tower A).triangle_rho] using ha
  obtain ⟨c,hc⟩ := (Triangle.mk C.lambdaMap C.rho C.delta).coyoneda_exact₂
    C.distinguished a hz
  change a = c ≫ C.lambdaMap at hc
  let e := verticalShiftEquiv (XModLambdaN A (N-i)) i m (w-i)
  let b := homotopyRegrade rfl (show w-i+i=w by omega) (e.symm c)
  have hb : homotopyRegrade rfl (show w=w-i+i by omega) b = e.symm c := by
    simp only [b,last_layer_regrade_trans]
    rfl
  have transport (B : SyntheticSpectrum) (m t v : ℤ) (h : t=v+i)
      (z : BiHom m t B) :
      homotopyRegrade (by simp) (by simp [h])
        (shiftHomotopyClass (0,-(i:ℤ)) (m,t) z) =
        verticalShiftEquiv B i m v (homotopyRegrade rfl h z) := by
    subst t
    simp [verticalShiftEquiv, AddEquiv.trans_apply, regradeAddEquiv,
      suspInvarianceAddEquiv, susp_invariance, shiftHomotopyClass, Iso.homCongr,
      homotopyRegrade]
  refine ⟨b,?_⟩
  simp only [finiteCoefficientShiftClass,show i ≠ 0 by omega,↓reduceDIte]
  rw [transport _ m w (w-i) (by omega),hb]
  exact (congrArg (fun z => z ≫ C.lambdaMap) (e.apply_symm_apply c)).trans hc.symm

end
end KIP126.ProofTools.Internal.SyntheticCoverage
