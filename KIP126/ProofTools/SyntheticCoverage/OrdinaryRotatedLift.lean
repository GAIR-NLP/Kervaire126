module

import all KIP126.ProofTools.SyntheticCoverage.HigherRotatedLift
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaShift
import all KIP126.ProofTools.MahowaldLeibniz.TerminalOrdinary

/-! Coefficient comparisons for the ordinary-first-arrow inverse rotation.
These reductions express compatibility on the full quotient inclusion. -/

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
set_option maxHeartbeats 2000000

/-- The lambda-map comparison is unchanged by a common actual bigraded
shift. The hypothesis is equality after the full quotient inclusion. -/
private theorem shifted_lambda_maps_equal_on_spheres
    (X Y : (AdamsObject (coefficients := background.coefficients))) (δ : ℤ×ℤ) (q d : ℕ) (hdq : d < q)
    (f g : (SyntheticCategory.biShift (0,-(d:ℤ))).obj
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (q-d)) ⟶
      XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (Y.obj background.auxiliary))) q)
    (hfg : (SyntheticCategory.biShift (0,-(d:ℤ))).map (XModLambdaN.incl _ (q-d)) ≫ f =
      (SyntheticCategory.biShift (0,-(d:ℤ))).map (XModLambdaN.incl _ (q-d)) ≫ g)
    (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift (0,-(d:ℤ))).obj
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (q-d)))) : c ≫ f=c ≫ g := by
  letI := background.exactness.shiftCommShift δ
  letI := background.exactness.shiftExact δ
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let K := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(d:ℤ))
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let B := background.nu.functor.obj (Y.obj background.auxiliary)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists background.quotients.coherence δ (q-d) A
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists background.quotients.coherence δ q B
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let C := shiftCommIso δ (0,-(d:ℤ))
  let f₀ : K.obj (XModLambdaN A (q-d)) ⟶ XModLambdaN B q :=
    ff.preimage (C.inv.app _ ≫ K.map εn.inv ≫ f ≫ εq.hom)
  let g₀ : K.obj (XModLambdaN A (q-d)) ⟶ XModLambdaN B q :=
    ff.preimage (C.inv.app _ ≫ K.map εn.inv ≫ g ≫ εq.hom)
  have hf₀ : F.map f₀=C.inv.app _ ≫ K.map εn.inv ≫ f ≫ εq.hom := ff.map_preimage _
  have hg₀ : F.map g₀=C.inv.app _ ≫ K.map εn.inv ≫ g ≫ εq.hom := ff.map_preimage _
  have hbase : K.map (XModLambdaN.incl A (q-d)) ≫ f₀=
      K.map (XModLambdaN.incl A (q-d)) ≫ g₀ := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hf₀,hg₀]
    have hn : F.map (K.map (XModLambdaN.incl A (q-d))) ≫ C.inv.app _=
        C.inv.app A ≫ K.map (F.map (XModLambdaN.incl A (q-d))) :=
      C.inv.naturality (XModLambdaN.incl A (q-d))
    simp only [←Category.assoc] at hn ⊢
    rw [hn,←hεn,Functor.map_comp]
    simp only [Category.assoc,←Functor.map_comp,Iso.hom_inv_id,
      Category.comp_id]
    rw [←Category.assoc (K.map (XModLambdaN.incl _ (q-d))),hfg]
    simp only [Category.assoc]
    rfl
  have h := finite_lambda_maps_equal_on_spheres X Y q d hdq f₀ g₀ hbase
  have h' := shift_preserves_sphere_congruence _ _ δ f₀ g₀ h m w
    (c ≫ K.map εn.hom ≫ C.hom.app _)
  rw [hf₀,hg₀] at h'
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc] at h'
  have he : K.map εn.hom ≫ K.map εn.inv=𝟙 _ := by
    rw [←Functor.map_comp,εn.hom_inv_id,CategoryTheory.Functor.map_id]
  rw [←Category.assoc (K.map εn.hom),he,Category.id_comp,
    ←Category.assoc (K.map εn.hom),he,Category.id_comp] at h'
  exact (cancel_mono εq.hom).mp (by simpa only [Category.assoc] using h')


/-- The three quotient inclusions give a map from the full rotated triangle
to the finite row, using the specified suspension inclusion comparison. -/
private def finite_row_inclusion
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (q : ℕ)
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ q)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ q ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q)) :
    (normalizedTriangle background T he).rotate ⟶ earlyFiniteRow T he q ey where
  hom₁ := XModLambdaN.incl _ q
  hom₂ := XModLambdaN.incl _ q
  hom₃ := XModLambdaN.incl _ q
  comm₁ := XModLambdaN.incl_naturality _ q
  comm₂ := XModLambdaN.incl_naturality _ q
  comm₃ := by
    symm
    change XModLambdaN.incl _ q ≫
      (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) q ≫ ey.hom)) =
      (-(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q)
    rw [Preadditive.comp_neg,Preadditive.neg_comp]
    congr 1
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,hey]


/-- Vanishing of the restriction error in both remaining exponent patterns
when the first exponent is zero. -/
private theorem ordinary_rotated_restriction_no_return
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (i : ℕ) (hi : 0 < i) (m w : ℤ)
    (d : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i))))
    (z : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i)) ⟶
      XModLambdaN (normalizedTriangle background T he).obj₃ i) : d ≫ z = 0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let eg : ℤ := normalizedExponent background.classicalTower T.g
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  letI := background.exactness.shiftCommShift (0,-eg)
  letI := background.exactness.shiftExact (0,-eg)
  obtain ⟨εD,_,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) (i+1-i)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨εC,_,_⟩ := quotient_shift_exists background.quotients.coherence (0,-eg) i
    (background.nu.functor.obj (T.Z.obj background.auxiliary))
  let eD := F.mapIso ((background.quotients.functoriality.functor (i+1-i)).mapIso
    (normalizedSuspensionZeroIso T he hf) ≪≫ εD) ≪≫
      (biShiftAddIso (1,0) (0,-(i:ℤ)) (1,-(i:ℤ)) (by ext <;> simp)).app _
  have hg : eg ≤ 1 := by
    dsimp [eg]
    exact_mod_cast normalizedExponent_le_one background.classicalTower T.g
  have h := shifted_finite_no_return T.X T.Z (i+1-i) i (by omega) hi
    (1,-(i:ℤ)) (0,-eg) (by dsimp; omega) m w (d ≫ eD.hom) (eD.inv ≫ z ≫ εC.hom)
  have h' := congrArg (fun a => a ≫ εC.inv) h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,
    Category.comp_id,zero_comp] using h'


/-- The ordinary inverse rotation supplies the prescribed restriction
and a top defect map selected before the sphere representative. -/
private theorem ordinary_raw_rotated_lift_with_top_defect
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (i : ℕ) (hi : 0 < i)
    (ey₁ : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (i+1-i))⟦(1:ℤ)⟧)
    (ey₂ : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (i+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (i+1))⟦(1:ℤ)⟧)
    (hrow₁ : earlyFiniteRow T he (i+1-i) ey₁ ∈ distTriang SyntheticSpectrum)
    (hrow₂ : earlyFiniteRow T he (i+1) ey₂ ∈ distTriang SyntheticSpectrum) :
    letI := background.exactness.shiftCommShift (0,-(i:ℤ))
    let N := normalizedTriangle background T he
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let L := F.mapTriangle.obj (earlyFiniteRow T he (i+1-i) ey₁)
    let CB := (background.quotients.tower N.obj₂).triangle hi (show i < i+1 by omega)
    let CD := (background.quotients.tower (N.obj₁⟦(1:ℤ)⟧)).triangle hi (show i < i+1 by omega)
    ∃ z : L.obj₁⟦(1:ℤ)⟧ ⟶ XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (i+1),
      ∀ (m w : ℤ) (a : BiHom m w (XModLambdaN N.obj₂ i))
        (d : BiHom m w L.obj₃),
        a ≫ CB.delta = -(d ≫ L.mor₃) →
        ∃ R : BiHom m w (XModLambdaN N.obj₃ (i+1)),
          R ≫ (background.quotients.tower N.obj₃).rho i (i+1) (by omega) =
            a ≫ XModLambdaN.map N.mor₂ i ∧
          R ≫ XModLambdaN.map N.mor₃ (i+1) =
            d ≫ CD.lambdaMap + (d ≫ L.mor₃) ≫ z := by
  letI := background.exactness.syntheticTriangulated
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  letI := background.exactness.shiftExact (0,-(i:ℤ))
  let N := normalizedTriangle background T he
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let L := F.mapTriangle.obj (earlyFiniteRow T he (i+1-i) ey₁)
  let U := earlyFiniteRow T he (i+1) ey₂
  let CB := (background.quotients.tower N.obj₂).triangle hi (show i < i+1 by omega)
  let CC := (background.quotients.tower N.obj₃).triangle hi (show i < i+1 by omega)
  let CD := (background.quotients.tower (N.obj₁⟦(1:ℤ)⟧)).triangle hi (show i < i+1 by omega)
  have hL : L ∈ distTriang SyntheticSpectrum := F.map_distinguished _ hrow₁
  obtain ⟨lD,hlD,hTail⟩ := complete_distinguished_triangle_morphism L U hL hrow₂
    CB.lambdaMap CC.lambdaMap
    ((background.quotients.natural N.mor₂).lambda_naturality hi (show i < i+1 by omega))
  let φ : L ⟶ U :=
    { hom₁ := CB.lambdaMap
      hom₂ := CC.lambdaMap
      hom₃ := lD
      comm₁ := (background.quotients.natural N.mor₂).lambda_naturality hi (show i < i+1 by omega)
      comm₂ := hlD
      comm₃ := hTail }
  let lambdaD : L.obj₃ ⟶ U.obj₃ := CD.lambdaMap
  have hdiff : L.mor₂ ≫ (lD-lambdaD)=0 := by
    rw [Preadditive.comp_sub,hlD]
    change CC.lambdaMap ≫ XModLambdaN.map N.mor₃ (i+1) -
      F.map (XModLambdaN.map N.mor₃ (i+1-i)) ≫ CD.lambdaMap = 0
    exact sub_eq_zero.mpr ((background.quotients.natural N.mor₃).lambda_naturality
      hi (show i < i+1 by omega)).symm
  obtain ⟨z,hz⟩ := L.yoneda_exact₃ hL (lD-lambdaD) hdiff
  refine ⟨z,?_⟩
  intro m w a d had
  have hRho : U.mor₁ ≫ (background.quotients.tower N.obj₃).rho i (i+1) (by omega) =
      CB.rho ≫ XModLambdaN.map N.mor₂ i := by
    rw [(background.quotients.tower N.obj₂).triangle_rho]
    exact ((background.quotients.natural N.mor₂).rho_naturality (show i ≤ i+1 by omega)).symm
  obtain ⟨R,hR,hRh⟩ := inverse_rotated_common_lift L U hrow₂ φ CB.rho CB.delta
    ((background.quotients.tower N.obj₃).rho i (i+1) (by omega)) (XModLambdaN.map N.mor₂ i)
    CB.distinguished hRho m w
    (fun d z => ordinary_rotated_restriction_no_return T he hf i hi m w d z) a d had
  refine ⟨R,hR,?_⟩
  have hΔ : d ≫ lD - d ≫ lambdaD = (d ≫ L.mor₃) ≫ z := by
    simpa only [Preadditive.comp_sub,Category.assoc] using congrArg (fun f => d ≫ f) hz
  have hsame : d ≫ lD = d ≫ lambdaD + (d ≫ L.mor₃) ≫ z := by
    rw [←hΔ]
    abel
  exact hRh.trans hsame


end
end KIP126.ProofTools.Internal.SyntheticCoverage
