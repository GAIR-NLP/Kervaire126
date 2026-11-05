module

import all KIP126.ProofTools.SyntheticCoverage.EarlyRotatedLift

import all KIP126.ProofTools.SyntheticCoverage.PositivePermanence
import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle

/-! Inverse-rotated coefficient lifts at positive coefficient lengths.
The lower rows are Q₁, the upper row is Q_(i+1), and the input lies
in Q_i. No-return comparisons use the sphere maps with
the specified shift commutation. -/

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
set_option maxHeartbeats 2500000

/-- Inverse rotation preserves both outputs of the octahedral lift and
the third component of its row morphism, with the chosen suspension comparison. -/
private theorem higher_rotated_restriction_no_return
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (i : ℕ) (hi : 0 < i) (m w : ℤ)
    (d : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i))))
    (z : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i)) ⟶
      XModLambdaN (normalizedTriangle background T he).obj₃ i) : d ≫ z = 0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let eD := F.mapIso ((background.quotients.functoriality.functor (i+1-i)).mapIso
    (normalizedSuspensionNativeIso T he hf))
  let eC := (background.quotients.functoriality.functor i).mapIso
    (normalizedThirdZeroIso T he hg) ≪≫ SyntheticCategory.biShift_zero.symm.app _
  have h := shifted_finite_no_return (.shift 1 T.X) T.Z (i+1-i) i (by omega) hi
    (0,-(i:ℤ)) (0,0) (by dsimp; omega) m w (d ≫ eD.hom) (eD.inv ≫ z ≫ eC.hom)
  have h' := congrArg (fun a => a ≫ eC.inv) h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,
    Category.comp_id,zero_comp] using h'

private theorem higher_rotated_filling_no_return
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (i : ℕ) (hi : 0 < i) (m w : ℤ)
    (d : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₂ (i+1-i)))⟦(1:ℤ)⟧))
    (z : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₂ (i+1-i)))⟦(1:ℤ)⟧) ⟶
      XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1)) : d ≫ z = 0 := by
  let B := XModLambdaN (normalizedTriangle background T he).obj₂ (i+1-i)
  let eB : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj B)⟦(1:ℤ)⟧) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj B :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (biShiftAddIso (0,-(i:ℤ)) (1,0) (1,-(i:ℤ)) (by ext <;> simp)).app B
  let eD := (background.quotients.functoriality.functor (i+1)).mapIso
    (normalizedSuspensionNativeIso T he hf) ≪≫ SyntheticCategory.biShift_zero.symm.app _
  have h := shifted_finite_no_return T.Y (.shift 1 T.X) (i+1-i) (i+1) (by omega) (by omega)
    (1,-(i:ℤ)) (0,0) (by dsimp; omega) m w (d ≫ eB.hom) (eB.inv ≫ z ≫ eD.hom)
  have h' := congrArg (fun a => a ≫ eD.inv) h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,
    Category.comp_id,zero_comp] using h'

private theorem higher_positive_raw_rotated_lift
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (i : ℕ) (hi : 0 < i)
    (ey₁ : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (i+1-i))⟦(1:ℤ)⟧)
    (ey₂ : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (i+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (i+1))⟦(1:ℤ)⟧)
    (hrow₁ : earlyFiniteRow T he (i+1-i) ey₁ ∈ distTriang SyntheticSpectrum)
    (hrow₂ : earlyFiniteRow T he (i+1) ey₂ ∈ distTriang SyntheticSpectrum)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₂ i))
    (d : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i))))
    (had : letI := background.exactness.shiftCommShift (0,-(i:ℤ))
      a ≫ ((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle
        (show 0 < i by omega) (show i < i+1 by omega)).delta =
        -(d ≫ ((SyntheticCategory.biShift (0,-(i:ℤ))).mapTriangle.obj
          (earlyFiniteRow T he (i+1-i) ey₁)).mor₃)) :
    ∃ R : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
      R ≫ (background.quotients.tower _).rho i (i+1) (by omega) =
        a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₂ i ∧
      R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1) =
        d ≫ ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
          (show 0 < i by omega) (show i < i+1 by omega)).lambdaMap := by
  letI := background.exactness.syntheticTriangulated
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  letI := background.exactness.shiftExact (0,-(i:ℤ))
  let N := normalizedTriangle background T he
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let L := F.mapTriangle.obj (earlyFiniteRow T he (i+1-i) ey₁)
  let U := earlyFiniteRow T he (i+1) ey₂
  let CB := (background.quotients.tower N.obj₂).triangle (show 0 < i by omega) (show i < i+1 by omega)
  let CC := (background.quotients.tower N.obj₃).triangle (show 0 < i by omega) (show i < i+1 by omega)
  let CD := (background.quotients.tower (N.obj₁⟦(1:ℤ)⟧)).triangle (show 0 < i by omega) (show i < i+1 by omega)
  have hL : L ∈ distTriang SyntheticSpectrum := F.map_distinguished _ hrow₁
  obtain ⟨lD,hlD,hTail⟩ := complete_distinguished_triangle_morphism L U hL hrow₂
    CB.lambdaMap CC.lambdaMap
    ((background.quotients.natural N.mor₂).lambda_naturality (show 0 < i by omega) (show i < i+1 by omega))
  let φ : L ⟶ U :=
    { hom₁ := CB.lambdaMap
      hom₂ := CC.lambdaMap
      hom₃ := lD
      comm₁ := (background.quotients.natural N.mor₂).lambda_naturality (show 0 < i by omega) (show i < i+1 by omega)
      comm₂ := hlD
      comm₃ := hTail }
  let lambdaD : L.obj₃ ⟶ U.obj₃ := CD.lambdaMap
  have hdiff : L.mor₂ ≫ (lD-lambdaD)=0 := by
    rw [Preadditive.comp_sub,hlD]
    change CC.lambdaMap ≫ XModLambdaN.map N.mor₃ (i+1) -
      F.map (XModLambdaN.map N.mor₃ (i+1-i)) ≫ CD.lambdaMap = 0
    exact sub_eq_zero.mpr ((background.quotients.natural N.mor₃).lambda_naturality
      (show 0 < i by omega) (show i < i+1 by omega)).symm
  obtain ⟨z,hz⟩ := L.yoneda_exact₃ hL (lD-lambdaD) hdiff
  have hsame : d ≫ lD = d ≫ lambdaD := by
    apply sub_eq_zero.mp
    rw [←Preadditive.comp_sub,hz,←Category.assoc]
    exact higher_rotated_filling_no_return T he hf i hi m w (d ≫ L.mor₃) z
  have hRho : U.mor₁ ≫ (background.quotients.tower N.obj₃).rho i (i+1) (by omega) =
      CB.rho ≫ XModLambdaN.map N.mor₂ i := by
    rw [(background.quotients.tower N.obj₂).triangle_rho]
    exact ((background.quotients.natural N.mor₂).rho_naturality (show i ≤ i+1 by omega)).symm
  obtain ⟨R,hR,hRh⟩ := inverse_rotated_common_lift L U hrow₂ φ CB.rho CB.delta
    ((background.quotients.tower N.obj₃).rho i (i+1) (by omega)) (XModLambdaN.map N.mor₂ i)
    CB.distinguished hRho m w
    (fun d z => higher_rotated_restriction_no_return T he hf hg i hi m w d z) a d had
  exact ⟨R,hR,hRh.trans hsame⟩


private def higherRotatedInput
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (i : ℕ)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧)
    (m w : ℤ)
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i)))⟦(1:ℤ)⟧)) :
    BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i))) := by
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  exact b ≫ (Functor.commShiftIso (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ)))
    (1:ℤ)).inv.app _ ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map ex.inv

private theorem higher_rotated_input_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (i : ℕ)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (i+1-i))⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ (i+1-i) ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1-i)))
    (hey : XModLambdaN.incl _ (i+1-i) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1-i)))
    (m w : ℤ)
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i)))⟦(1:ℤ)⟧)) :
    letI := background.exactness.shiftCommShift (0,-(i:ℤ));
    -(higherRotatedInput T he i ex m w b ≫
      ((SyntheticCategory.biShift (0,-(i:ℤ))).mapTriangle.obj (earlyFiniteRow T he (i+1-i) ey)).mor₃) =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₁ (i+1-i))) := by
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  let N := normalizedTriangle background T he
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let κ := Functor.commShiftIso F (1:ℤ)
  let d := higherRotatedInput T he i ex m w b
  have hs (m' w' : ℤ) (c : BiHom m' w' (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (i+1-i))) :
      c ≫ (XModLambdaN.map (S.map N.mor₁) (i+1-i) ≫ ey.hom) =
        c ≫ (ex.hom ≫ S.map (XModLambdaN.map N.mor₁ (i+1-i))) := by
    exact finite_suspension_normalized_map_on_spheres T.X T.Y
      (normalizedExponent background.classicalTower T.f) (by omega) (i+1-i) (by omega)
      N.mor₁ ex ey hex hey m' w' c
  have h := shift_preserves_sphere_congruence _ _ (0,-(i:ℤ)) _ _ hs m w d
  have h' := congrArg (fun a => a ≫ κ.hom.app (XModLambdaN N.obj₂ (i+1-i))) h
  simp only [Functor.map_comp,Category.assoc] at h'
  have hn : F.map (S.map (XModLambdaN.map N.mor₁ (i+1-i))) ≫ κ.hom.app (XModLambdaN N.obj₂ (i+1-i)) =
      κ.hom.app (XModLambdaN N.obj₁ (i+1-i)) ≫ S.map (F.map (XModLambdaN.map N.mor₁ (i+1-i))) :=
    κ.hom.naturality (XModLambdaN.map N.mor₁ (i+1-i))
  rw [hn] at h'
  have hd : d ≫ F.map ex.hom = b ≫ κ.inv.app (XModLambdaN N.obj₁ (i+1-i)) := by
    change (b ≫ κ.inv.app _ ≫ F.map ex.inv) ≫ F.map ex.hom = _
    rw [Category.assoc,Category.assoc,←Functor.map_comp,ex.inv_hom_id,CategoryTheory.Functor.map_id]
    exact congrArg (fun k => b ≫ k) (Category.comp_id _)
  rw [←Category.assoc d (F.map ex.hom),hd] at h'
  simp only [Category.assoc,Iso.inv_hom_id_app_assoc] at h'
  change -(d ≫ F.map (-(XModLambdaN.map (S.map N.mor₁) (i+1-i) ≫ ey.hom)) ≫
    κ.hom.app (XModLambdaN N.obj₂ (i+1-i))) = _
  simpa only [Functor.map_neg,Functor.map_comp,Preadditive.comp_neg,
    Preadditive.neg_comp,neg_neg,Category.assoc] using h'

/-- The specified rows give both finite distinguished rows. The finite
delta–first-map square constructs R with its two prescribed images. -/
private theorem higher_positive_rotated_of_finite_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (i : ℕ) (hi : 0 < i) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₂ i))
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i)))⟦(1:ℤ)⟧))
    (hab : a ≫ ((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle
        (show 0 < i by omega) (show i < i+1 by omega)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₁ (i+1-i)))) :
    ∃ (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧),
      XModLambdaN.incl _ (i+1-i) ≫ ex.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1-i)) ∧
      ∃ R : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
        R ≫ (background.quotients.tower _).rho i (i+1) (by omega) =
          a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₂ i ∧
        R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1) =
          higherRotatedInput T he i ex m w b ≫
            ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
              (show 0 < i by omega) (show i < i+1 by omega)).lambdaMap := by
  obtain ⟨ey₁,hey₁,hrow₁⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (i+1-i) (by omega)
  obtain ⟨ey₂,hey₂,hrow₂⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (i+1) (by omega)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists (normalizedTriangle background T he).obj₁ (i+1-i)
  obtain ⟨R,hR,hRh⟩ := higher_positive_raw_rotated_lift T he hf hg i hi ey₁ ey₂ hrow₁ hrow₂
    m w a (higherRotatedInput T he i ex m w b)
    (hab.trans (higher_rotated_input_square T he hf i ex ey₁ hex hey₁ m w b).symm)
  exact ⟨ex,hex,R,hR,hRh⟩


end
end KIP126.ProofTools.Internal.SyntheticCoverage
