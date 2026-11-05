module

import all KIP126.ProofTools.SyntheticCoverage.PositivePermanence
import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle

/-! The rotated finite common lift for the early-boundary construction.
The selected quotient rows are rotated as actual triangles. Comparisons of
chosen fillings are made only after evaluation on sphere representatives. -/

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
private theorem inverse_rotated_common_lift
    (L U : Triangle SyntheticSpectrum) (hU : U ∈ distTriang SyntheticSpectrum)
    (φ : L ⟶ U) {ZA CA : SyntheticSpectrum}
    (rhoB : U.obj₁ ⟶ ZA) (deltaB : ZA ⟶ L.obj₁⟦(1:ℤ)⟧)
    (rhoC : U.obj₂ ⟶ CA) (gA : ZA ⟶ CA)
    (hB : Triangle.mk φ.hom₁ rhoB deltaB ∈ distTriang SyntheticSpectrum)
    (hRho : U.mor₁ ≫ rhoC = rhoB ≫ gA)
    (m w : ℤ)
    (hNoReturn : ∀ (d : BiHom m w L.obj₃) (z : L.obj₃ ⟶ CA), d ≫ z = 0)
    (a : BiHom m w ZA) (d : BiHom m w L.obj₃)
    (had : a ≫ deltaB = -(d ≫ L.mor₃)) :
    ∃ R : BiHom m w U.obj₂,
      R ≫ rhoC = a ≫ gA ∧ R ≫ U.mor₂ = d ≫ φ.hom₃ := by
  letI := background.exactness.syntheticTriangulated
  let κ := (shiftEquiv SyntheticSpectrum (1:ℤ)).counitIso
  let ψ := (invRotate SyntheticSpectrum).map φ
  let b : BiHom m w (L.invRotate.obj₁⟦(1:ℤ)⟧) := d ≫ κ.inv.app L.obj₃
  have hRot : -(shiftFunctor SyntheticSpectrum (1:ℤ)).map L.invRotate.mor₁ =
      κ.hom.app L.obj₃ ≫ L.mor₃ := by
    simpa [κ,invRotCompRot,Triangle.rotate] using
      (((invRotCompRot (C:=SyntheticSpectrum)).app L).hom.comm₃)
  have hab : a ≫ deltaB = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      L.invRotate.mor₁ := by
    rw [had]
    have h := congrArg (fun f => b ≫ f) hRot
    simp only [Preadditive.comp_neg,b,Category.assoc,Iso.inv_hom_id_app_assoc] at h
    simpa only [b,Category.assoc] using (neg_eq_iff_eq_neg.mp h).symm
  obtain ⟨R,hR,hRk⟩ := ThreeByThree.common_lift_of_no_return
    L.invRotate.mor₁ φ.hom₁ ψ.hom₁ U.invRotate.mor₁ U.invRotate.mor₂
    U.invRotate.mor₃ rhoB deltaB gA rhoC hB
    (inv_rot_of_distTriang U hU) ψ.comm₁.symm hRho
    (fun b z => by
      have h := hNoReturn (b ≫ κ.hom.app L.obj₃) (κ.inv.app L.obj₃ ≫ z)
      simpa only [Category.assoc,Iso.hom_inv_id_app_assoc] using h)
    a b hab
  change BiHom m w U.obj₂ at R
  refine ⟨R,hR,?_⟩
  have h := congrArg (fun f => f ≫ κ.hom.app U.obj₃) hRk
  change (R ≫ (U.mor₂ ≫ κ.inv.app U.obj₃)) ≫ κ.hom.app U.obj₃ =
    (b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((shiftFunctor SyntheticSpectrum (-1:ℤ)).map φ.hom₃)) ≫ κ.hom.app U.obj₃ at h
  simp only [Category.assoc,Iso.inv_hom_id_app] at h
  have hn : (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((shiftFunctor SyntheticSpectrum (-1:ℤ)).map φ.hom₃) ≫ κ.hom.app U.obj₃ =
      κ.hom.app L.obj₃ ≫ φ.hom₃ := κ.hom.naturality φ.hom₃
  rw [hn] at h
  simpa only [b,Functor.id_obj,Category.assoc,Iso.inv_hom_id_app_assoc,Category.comp_id] using h


private def earlyFiniteRow
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (q : ℕ)
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ q)⟦(1:ℤ)⟧) :
    Triangle SyntheticSpectrum :=
  Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
    (XModLambdaN.map (normalizedTriangle background T he).mor₃ q)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) q ≫ ey.hom))

/-- The two no-return gaps needed by inverse rotation. The first is a
restriction defect; the second compares the TR3 filling with the selected
coefficient inclusion. Both statements concern evaluated sphere maps. -/
private theorem early_rotated_restriction_no_return
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (m w : ℤ)
    (d : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1)))
    (z : (SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1) ⟶
      XModLambdaN (normalizedTriangle background T he).obj₃ 1) : d ≫ z = 0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let eD := F.mapIso ((background.quotients.functoriality.functor 1).mapIso
    (normalizedSuspensionNativeIso T he hf))
  let eC := (background.quotients.functoriality.functor 1).mapIso
    (normalizedThirdZeroIso T he hg) ≪≫ SyntheticCategory.biShift_zero.symm.app _
  have h := shifted_finite_no_return (.shift 1 T.X) T.Z 1 1 (by decide) (by decide)
    (0,-1) (0,0) (by norm_num) m w (d ≫ eD.hom) (eD.inv ≫ z ≫ eC.hom)
  have h' := congrArg (fun a => a ≫ eC.inv) h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,
    Category.comp_id,zero_comp] using h'

private theorem early_rotated_filling_no_return
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (m w : ℤ)
    (d : BiHom m w (((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (normalizedTriangle background T he).obj₂ 1))⟦(1:ℤ)⟧))
    (z : (((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (normalizedTriangle background T he).obj₂ 1))⟦(1:ℤ)⟧) ⟶
      XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 2) : d ≫ z = 0 := by
  let B := XModLambdaN (normalizedTriangle background T he).obj₂ 1
  let eB : (((SyntheticCategory.biShift (0,-1)).obj B)⟦(1:ℤ)⟧) ≅
      (SyntheticCategory.biShift (1,-1)).obj B :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (biShiftAddIso (0,-1) (1,0) (1,-1) (by decide)).app B
  let eD := (background.quotients.functoriality.functor 2).mapIso
    (normalizedSuspensionNativeIso T he hf) ≪≫ SyntheticCategory.biShift_zero.symm.app _
  have h := shifted_finite_no_return T.Y (.shift 1 T.X) 1 2 (by decide) (by decide)
    (1,-1) (0,0) (by norm_num) m w (d ≫ eB.hom) (eB.inv ≫ z ≫ eD.hom)
  have h' := congrArg (fun a => a ≫ eD.inv) h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,
    Category.comp_id,zero_comp] using h'

/-- Construct the rotated lift on the actual selected quotient objects.
The row premises are supplied by the specified Literature theorem at levels
one and two. The TR3 third component is compared with the actual lambda map
only on spheres, using the second no-return gap above. -/
private theorem early_positive_raw_rotated_lift
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (ey₁ : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ 1)⟦(1:ℤ)⟧)
    (ey₂ : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) 2 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ 2)⟦(1:ℤ)⟧)
    (hrow₁ : earlyFiniteRow T he 1 ey₁ ∈ distTriang SyntheticSpectrum)
    (hrow₂ : earlyFiniteRow T he 2 ey₂ ∈ distTriang SyntheticSpectrum)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₂ 1))
    (d : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1)))
    (had : letI := background.exactness.shiftCommShift (0,-1)
      a ≫ ((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle
        (show 0<1 by decide) (show 1<2 by decide)).delta =
        -(d ≫ ((SyntheticCategory.biShift (0,-1)).mapTriangle.obj
          (earlyFiniteRow T he 1 ey₁)).mor₃)) :
    ∃ R : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ 2),
      R ≫ (background.quotients.tower _).rho 1 2 (by decide) =
        a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₂ 1 ∧
      R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 =
        d ≫ ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
          (show 0<1 by decide) (show 1<2 by decide)).lambdaMap := by
  letI := background.exactness.syntheticTriangulated
  letI := background.exactness.shiftCommShift (0,-1)
  letI := background.exactness.shiftExact (0,-1)
  let N := normalizedTriangle background T he
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let L := F.mapTriangle.obj (earlyFiniteRow T he 1 ey₁)
  let U := earlyFiniteRow T he 2 ey₂
  let CB := (background.quotients.tower N.obj₂).triangle (show 0<1 by decide) (show 1<2 by decide)
  let CC := (background.quotients.tower N.obj₃).triangle (show 0<1 by decide) (show 1<2 by decide)
  let CD := (background.quotients.tower (N.obj₁⟦(1:ℤ)⟧)).triangle (show 0<1 by decide) (show 1<2 by decide)
  have hL : L ∈ distTriang SyntheticSpectrum := F.map_distinguished _ hrow₁
  obtain ⟨lD,hlD,hTail⟩ := complete_distinguished_triangle_morphism L U hL hrow₂
    CB.lambdaMap CC.lambdaMap
    ((background.quotients.natural N.mor₂).lambda_naturality (show 0<1 by decide) (show 1<2 by decide))
  let φ : L ⟶ U :=
    { hom₁ := CB.lambdaMap
      hom₂ := CC.lambdaMap
      hom₃ := lD
      comm₁ := (background.quotients.natural N.mor₂).lambda_naturality (show 0<1 by decide) (show 1<2 by decide)
      comm₂ := hlD
      comm₃ := hTail }
  let lambdaD : L.obj₃ ⟶ U.obj₃ := CD.lambdaMap
  have hdiff : L.mor₂ ≫ (lD-lambdaD)=0 := by
    rw [Preadditive.comp_sub,hlD]
    change CC.lambdaMap ≫ XModLambdaN.map N.mor₃ 2 -
      F.map (XModLambdaN.map N.mor₃ 1) ≫ CD.lambdaMap = 0
    exact sub_eq_zero.mpr ((background.quotients.natural N.mor₃).lambda_naturality
      (show 0<1 by decide) (show 1<2 by decide)).symm
  obtain ⟨z,hz⟩ := L.yoneda_exact₃ hL (lD-lambdaD) hdiff
  have hsame : d ≫ lD = d ≫ lambdaD := by
    apply sub_eq_zero.mp
    rw [←Preadditive.comp_sub,hz,←Category.assoc]
    exact early_rotated_filling_no_return T he hf m w (d ≫ L.mor₃) z
  have hRho : U.mor₁ ≫ (background.quotients.tower N.obj₃).rho 1 2 (by decide) =
      CB.rho ≫ XModLambdaN.map N.mor₂ 1 := by
    rw [(background.quotients.tower N.obj₂).triangle_rho]
    exact ((background.quotients.natural N.mor₂).rho_naturality (show 1≤2 by decide)).symm
  obtain ⟨R,hR,hRh⟩ := inverse_rotated_common_lift L U hrow₂ φ CB.rho CB.delta
    ((background.quotients.tower N.obj₃).rho 1 2 (by decide)) (XModLambdaN.map N.mor₂ 1)
    CB.distinguished hRho m w
    (fun d z => early_rotated_restriction_no_return T he hf hg m w d z) a d had
  exact ⟨R,hR,hRh.trans hsame⟩


/-- Input for the inverse-rotated row, retaining its ordinary shift
commutation for top-label calibration. -/
private def earlyRotatedInput
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1)⟦(1:ℤ)⟧)
    (m w : ℤ)
    (b : BiHom m w (((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1))⟦(1:ℤ)⟧)) :
    BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1)) := by
  letI := background.exactness.shiftCommShift (0,-1)
  exact b ≫ (Functor.commShiftIso (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1))
    (1:ℤ)).inv.app _ ≫ (SyntheticCategory.biShift (0,-1)).map ex.inv

private theorem early_rotated_input_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ 1)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ 1 ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1))
    (hey : XModLambdaN.incl _ 1 ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1))
    (m w : ℤ)
    (b : BiHom m w (((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1))⟦(1:ℤ)⟧)) :
    letI := background.exactness.shiftCommShift (0,-1);
    -(earlyRotatedInput T he ex m w b ≫
      ((SyntheticCategory.biShift (0,-1)).mapTriangle.obj (earlyFiniteRow T he 1 ey)).mor₃) =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₁ 1)) := by
  letI := background.exactness.shiftCommShift (0,-1)
  let N := normalizedTriangle background T he
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let κ := Functor.commShiftIso F (1:ℤ)
  let d := earlyRotatedInput T he ex m w b
  have hs (m' w' : ℤ) (c : BiHom m' w' (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) 1)) :
      c ≫ (XModLambdaN.map (S.map N.mor₁) 1 ≫ ey.hom) =
        c ≫ (ex.hom ≫ S.map (XModLambdaN.map N.mor₁ 1)) := by
    exact finite_suspension_normalized_map_on_spheres T.X T.Y
      (normalizedExponent background.classicalTower T.f) (by omega) 1 (by decide)
      N.mor₁ ex ey hex hey m' w' c
  have h := shift_preserves_sphere_congruence _ _ (0,-1) _ _ hs m w d
  have h' := congrArg (fun a => a ≫ κ.hom.app (XModLambdaN N.obj₂ 1)) h
  simp only [Functor.map_comp,Category.assoc] at h'
  have hn : F.map (S.map (XModLambdaN.map N.mor₁ 1)) ≫ κ.hom.app (XModLambdaN N.obj₂ 1) =
      κ.hom.app (XModLambdaN N.obj₁ 1) ≫ S.map (F.map (XModLambdaN.map N.mor₁ 1)) :=
    κ.hom.naturality (XModLambdaN.map N.mor₁ 1)
  rw [hn] at h'
  have hd : d ≫ F.map ex.hom = b ≫ κ.inv.app (XModLambdaN N.obj₁ 1) := by
    change (b ≫ κ.inv.app _ ≫ F.map ex.inv) ≫ F.map ex.hom = _
    rw [Category.assoc,Category.assoc,←Functor.map_comp,ex.inv_hom_id,CategoryTheory.Functor.map_id]
    exact congrArg (fun k => b ≫ k) (Category.comp_id _)
  rw [←Category.assoc d (F.map ex.hom),hd] at h'
  simp only [Category.assoc,Iso.inv_hom_id_app_assoc] at h'
  change -(d ≫ F.map (-(XModLambdaN.map (S.map N.mor₁) 1 ≫ ey.hom)) ≫
    κ.hom.app (XModLambdaN N.obj₂ 1)) = _
  simpa only [Functor.map_neg,Functor.map_comp,Preadditive.comp_neg,
    Preadditive.neg_comp,neg_neg,Category.assoc] using h'

/-- The specified rows give both finite distinguished rows. The finite
delta–first-map square constructs R with its two prescribed images. -/
private theorem early_positive_rotated_of_finite_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₂ 1))
    (b : BiHom m w (((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1))⟦(1:ℤ)⟧))
    (hab : a ≫ ((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle
        (show 0<1 by decide) (show 1<2 by decide)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₁ 1))) :
    ∃ (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1)⟦(1:ℤ)⟧),
      XModLambdaN.incl _ 1 ≫ ex.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1) ∧
      ∃ R : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ 2),
        R ≫ (background.quotients.tower _).rho 1 2 (by decide) =
          a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₂ 1 ∧
        R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 =
          earlyRotatedInput T he ex m w b ≫
            ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
              (show 0<1 by decide) (show 1<2 by decide)).lambdaMap := by
  obtain ⟨ey₁,hey₁,hrow₁⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he 1 (by decide)
  obtain ⟨ey₂,hey₂,hrow₂⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he 2 (by decide)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists (normalizedTriangle background T he).obj₁ 1
  obtain ⟨R,hR,hRh⟩ := early_positive_raw_rotated_lift T he hf hg ey₁ ey₂ hrow₁ hrow₂
    m w a (earlyRotatedInput T he ex m w b)
    (hab.trans (early_rotated_input_square T he hf ex ey₁ hex hey₁ m w b).symm)
  exact ⟨ex,hex,R,hR,hRh⟩


private def earlyNormalizedSourceLabel
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (u : Ambient background T.X (s,t)) :
    BiHom (t-s) (t+1) (XModLambdaN (normalizedTriangle background T he).obj₁ 1) :=
  (background.firstQuotient T.X 1 s t).symm u ≫
    XModLambdaN.map (normalizedPositiveSourceIso T hf).inv 1

private theorem early_normalized_source_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (u : Ambient background T.X (s,t)) :
    earlyNormalizedSourceLabel T he hf s t u ≫
      XModLambdaN.map (normalizedTriangle background T he).mor₁ 1 =
      (background.firstQuotient T.X 1 s t).symm u ≫ XModLambdaN.map (normalizedFirstMap T hf) 1 := by
  have hm : (normalizedPositiveSourceIso T hf).hom ≫ normalizedFirstMap T hf =
      (normalizedTriangle background T he).mor₁ := normalizedPositiveSourceIso_map T hf
  have hm' : (normalizedPositiveSourceIso T hf).inv ≫ (normalizedTriangle background T he).mor₁ =
      normalizedFirstMap T hf := by rw [←hm,Iso.inv_hom_id_assoc]
  dsimp only [earlyNormalizedSourceLabel]
  rw [Category.assoc,←background.quotients.functoriality.map_comp,hm']

private def earlyPositiveBoundaryInput
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (u : Ambient background T.X (s+1,t)) :
    BiHom (t-s) t (((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1))⟦(1:ℤ)⟧) :=
  (biSuspensionHomEquiv (t-s) t 1 (XModLambdaN (normalizedTriangle background T he).obj₁ 1)).symm
    (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
      (earlyNormalizedSourceLabel T he hf (s+1) t u))

/-- The specified E2 vector equation supplies the actual delta--first-map
square; it is not weakened to an equality after quotienting by boundaries. -/
private theorem early_classical_d2_positive_finite_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+1,t))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) t u)) :
    nativeFirstLabel T.Y s t c ≫
      ((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle
        (show 0<1 by decide) (show 1<2 by decide)).delta =
      earlyPositiveBoundaryInput T he hf s t u ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₁ 1)) := by
  obtain ⟨a,ha,hda⟩ := (differential_iff_specified_finite_lift T.Y 1 (by decide) s t c
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) t u)).mp hd
  have hae : a = nativeFirstLabel T.Y s t c := by
    simpa only [(background.quotients.tower _).rho_id,Category.comp_id] using ha
  rw [hae] at hda
  apply (biSuspensionHomEquiv (t-s) t 1
    (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).injective
  rw [bi_susp_natural background.quotients.coherence]
  change _ = (biSuspensionHomEquiv (t-s) t 1 _)
    ((biSuspensionHomEquiv (t-s) t 1 _).symm _) ≫ _
  rw [AddEquiv.apply_symm_apply,←regrade_comp,early_normalized_source_image]
  apply homotopy_regrade_injective
    (show (t-s)-1=(t+1)-(s+1+1) by omega) rfl
  rw [normalized_homotopy_regrade_trans]
  have hlabel := cofiberFirstQuotientBoundary_native_label T hf (s+1) t u
  have hda' := hda.trans hlabel
  convert hda' using 1 <;> rfl

/-- A prescribed early d2 boundary constructs one root at Q2, with its
literal first label G2c and a literal selected coefficient image. Only the
last transport to the native top label remains a separate comparison. -/
private theorem early_positive_rotated_of_d2
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (s t : ℤ) (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+1,t))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) t u)) :
    ∃ (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1)⟦(1:ℤ)⟧),
      XModLambdaN.incl _ 1 ≫ ex.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1) ∧
      ∃ R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ 2),
        R ≫ (background.quotients.tower _).rho 1 2 (by decide) =
          nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
            XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 ∧
        R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 =
          earlyRotatedInput T he ex (t-s) t (earlyPositiveBoundaryInput T he hf s t u) ≫
            ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
              (show 0<1 by decide) (show 1<2 by decide)).lambdaMap := by
  obtain ⟨ex,hex,R,hR,hRh⟩ := early_positive_rotated_of_finite_square T he hT hf hg
    (t-s) t (nativeFirstLabel T.Y s t c) (earlyPositiveBoundaryInput T he hf s t u)
    (early_classical_d2_positive_finite_square T he hf s t c u hd)
  refine ⟨ex,hex,R,?_,hRh⟩
  rw [hR,←native_first_label_natural,Category.assoc,←background.quotients.functoriality.map_comp]
  have hg' : background.nu.functor.map T.g ≫ (normalizedThirdZeroIso T he hg).inv =
      (normalizedTriangle background T he).mor₂ := by
    apply (cancel_mono (normalizedThirdZeroIso T he hg).hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      (normalized_second_arrow_zero T he hg).symm
  rw [hg']

end
end KIP126.ProofTools.Internal.SyntheticCoverage
