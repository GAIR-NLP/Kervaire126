module

import KIP126.Literature.E2Exactness
import KIP126.AdamsComputation.Moore.E2
import all KIP126.Main.Internal.Moore.Construction
import all KIP126.Main.Internal.Moore.ConstructionBoundary
import all KIP126.Main.Internal.Moore.FirstQuotientActionImage
import all KIP126.Main.Internal.Moore.H0SourceObstruction

/-! Nonvanishing of the Moore bottom source from the sphere differential,
using the normalized exact sequence and its Q₁ map. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.Main.Internal KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

private theorem moore_connecting_native_image
    (y : background.classical.sphere.Page 2 (7,131)) :
    ∃ b : BiHom 124 132 (XModLambdaN (Smn (Syn := SyntheticSpectrum) 0 1) 1),
      (sphereFirstQuotient background 8 132).symm
        (KIP126.Literature.Standard.E2Exactness.e2Connecting
          KIP126.AdamsComputation.Moore.triangle twoMap_exponent 7 131 y) =
        b ≫ XModLambdaN.map KIP126.Literature.Standard.syntheticH0 1 := by
  let a := (background.firstQuotient .sphere 1 7 131).symm y
  let F : (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj ((AdamsObject.sphere).obj background.auxiliary)) ⟶
        background.nu.functor.obj ((AdamsObject.sphere).obj background.auxiliary) := by
    simpa only [twoMap_exponent,Nat.cast_one] using
      (background.normalizedMap .sphere .sphere KIP126.AdamsComputation.Moore.twoMap).map
  have hF : F = selectedTwoNormalized := by
    have transport {A B : SyntheticSpectrum} (e : ℕ) (he : e=1)
        (f : (SyntheticCategory.biShift (0,(e:ℤ))).obj A ⟶ B) :
        (show (SyntheticCategory.biShift (0,1)).obj A ⟶ B from by
          simpa only [he,Nat.cast_one] using f) =
          eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj A)
            he.symm) ≫ f := by
      subst e
      simp only [eqToHom_refl,Category.id_comp]
      rfl
    exact transport _ twoMap_exponent
      (background.normalizedMap .sphere .sphere KIP126.AdamsComputation.Moore.twoMap).map
  refine ⟨a ≫ XModLambdaN.map
    ((SyntheticCategory.biShift (0,1)).map background.nu.unitIso.hom) 1,?_⟩
  have h := first_label_sphere_transport 8 132
    (KIP126.Literature.Standard.E2Exactness.e2Connecting
      KIP126.AdamsComputation.Moore.triangle twoMap_exponent 7 131 y)
  rw [←h]
  simp only [KIP126.Literature.Standard.E2Exactness.e2Connecting,firstLabel,
    KIP126.AdamsComputation.Moore.triangle,Int.reduceAdd,Int.reduceSub,
    LinearEquiv.symm_apply_apply,homotopyRegrade]
  change (a ≫ XModLambdaN.map F 1 ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app
        (background.nu.functor.obj SphereSpectrum)) 1) ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _ ≫ background.nu.unitIso.hom) 1 = _
  rw [hF,selectedTwoNormalized_eq_h0]
  have hz : XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app
      (background.nu.functor.obj (SphereSpectrum (C:=Spectrum)))) 1 ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app
        (background.nu.functor.obj (SphereSpectrum (C:=Spectrum)))) 1 = 𝟙 _ := by
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id_app,
      background.quotients.functoriality.map_id]
  have hu : XModLambdaN.map background.nu.unitIso.inv 1 ≫
      XModLambdaN.map background.nu.unitIso.hom 1 = 𝟙 _ := by
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id]
  simp only [h0NormalizedMap,background.quotients.functoriality.map_comp,Category.assoc]
  erw [reassoc_of% hz,hu,Category.comp_id]

private theorem moore_connecting_h0_image
    (y : background.classical.sphere.Page 2 (7,131)) :
    ∃ z : background.classical.sphere.Page 2 (7,131),
      KIP126.Computation.Standard.product (r := (8,132)) KIP126.Computation.Standard.h0 z =
        KIP126.Literature.Standard.E2Exactness.e2Connecting
          KIP126.AdamsComputation.Moore.triangle twoMap_exponent 7 131 y := by
  obtain ⟨b,hb⟩ := moore_connecting_native_image y
  obtain ⟨z,hz⟩ := first_quotient_h0_action_image b
  refine ⟨sphereFirstQuotient background 7 131 z,?_⟩
  have h := KIP126.Literature.Standard.first_quotient_action 1 1 7 131
    KIP126.Literature.Standard.syntheticH0 z
  change sphereFirstQuotient background 8 132
      (sphereAction KIP126.Literature.Standard.syntheticH0 z) =
    background.sphereAlgebra.product (1,1) (7,131)
      (KIP126.AdamsSynthetic.sphereFirstQuotient background.nu
        background.quotients.functoriality background.firstQuotient 1 1
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0))
      (sphereFirstQuotient background 7 131 z) at h
  rw [KIP126.Literature.Standard.syntheticH0_first_quotient_label,hz,←hb,LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Nonvanishing from the sphere d₂ calculation and normalized E₂ exact sequence. -/
private theorem moore_bottom_source_ne_zero :
    KIP126.AdamsComputation.Moore.bottomSource ≠ 0 := by
  intro hz
  have hg : (background.classical.map KIP126.AdamsComputation.Moore.bottom).pageMap
      2 (8,132) (KIP126.Computation.Table.basis .sphere 8 132 0) = 0 := hz
  obtain ⟨y,hy⟩ := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
    KIP126.AdamsComputation.Moore.triangle twoMap_exponent moore_cell_exponents.1
    moore_cell_exponents.2 7 131 (KIP126.Computation.Table.basis .sphere 8 132 0)).mp hg
  obtain ⟨z,hz⟩ := moore_connecting_h0_image y
  exact h0_source_not_in_image ⟨z,hz.trans hy⟩

end
end KIP126.Main.Internal.Moore
end
