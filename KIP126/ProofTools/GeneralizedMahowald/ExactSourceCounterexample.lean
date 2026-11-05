module
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuPremises
import all KIP126.ProofTools.GeneralizedMahowald.BottomNuInjection
import KIP126.Literature.Standard

/-! A refutation of the exact-source GeneralizedMahowaldLaw using the
rotated nu triangle, its extension premises and the nonzero bottom-map
leading image of d₂(h₄). -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option Elab.async false

private theorem zero_normalized_leading_nonzero (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (he : normalizedExponent background.classicalTower f=0)
    (x : Ambient background X (3,17))
    (hnu : familyPageMap background.family (background.nu.functor.map f) 2 (3,17,17)
      (nuWeightLabel background X 3 17 17 (by omega) x)≠0) :
    familyPageMap background.family (background.normalizedMap X Y f).map 2
      (3,(17-3)+3,17+normalizedExponent background.classicalTower f)
      (infiniteSourceForExtension background X Y f 3 17 x)≠0 := by
  have core (k : ℕ) (hk : k=0)
      (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
          background.nu.functor.obj (Y.obj background.auxiliary))
      (hM : lambdaToPositivePow k _≫M=background.nu.functor.map f) :
      familyPageMap background.family M 2 (3,(17-3)+3,17+k)
        (regradeE2 (by simp) (background.comparison.nuE2 X k 3 17 0 x))≠0 := by
    subst k
    rw [normalized_zero_map_form rfl M _ hM]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←family_page_comp,ModuleCat.comp_apply]
    exact hnu
  exact core _ he _ (background.normalizedMap X Y f).factorization


private theorem candidate_zero_differential :
    DifferentialAt background rotatedNuRouteTriangle.Z 3 (1,16) (4,18) 0 0 := by
  refine ⟨by decide,?_,0,0,RepresentsOnPage.zero (by decide),RepresentsOnPage.zero (by decide),?_⟩
  · rw [background.classical.differentialDegree]
    rfl
  · simp

/-- The geometric inputs and original hypotheses come from the
rotated-triangle comparisons. Only leading-image nonvanishing is explicit. -/
private theorem mh2_candidate_refutation_of_bottom_nonzero
    (hbottom : familyPageMap background.family
      (background.normalizedMap .sphere .nuCofiber rotatedNuRouteTriangle.f).map 2
      (3,(17-3)+3,17+normalizedExponent background.classicalTower rotatedNuRouteTriangle.f)
      (infiniteSourceForExtension background .sphere .nuCofiber rotatedNuRouteTriangle.f 3 17
        mh2BoundaryClass) ≠ 0) :
    GeneralizedMahowaldLaw background rotatedNuRouteTriangle → False := by
  intro hLaw
  have he := rotated_nu_exponent_sum
  have htriangle : NormalizedTriangleCompatible background rotatedNuRouteTriangle he :=
    rotated_nu_normalized_distinguished
  obtain ⟨sx,hsusp,hh,hcross,hg⟩ := rotated_nu_remaining_premises
  have hef := rotated_nu_f_exponent
  have heg := rotated_nu_g_exponent
  have heh : normalizedExponent background.classicalTower rotatedNuRouteTriangle.h=1 := by
    rw [hef,heg] at he
    omega
  have hx : IsCycle background .sphere 1 (3,17) mh2BoundaryClass :=
    ⟨by decide,boundaries_le_cycles background .sphere (3,17) 2 1 mh2BoundaryClass_boundary⟩
  have hy : IsCycle background .nuCofiber 1 (4,18) 0 := ⟨by decide,Submodule.zero_mem _⟩
  have hxBar : IsCycle background rotatedNuRouteTriangle.Z 2 (1,16) 0 :=
    ⟨by decide,Submodule.zero_mem _⟩
  have hyBar : IsPermanent background rotatedNuRouteTriangle.Z (4,18) 0 := Submodule.zero_mem _
  have H := hLaw he htriangle 1 0 2 1 16
  dsimp only at H
  norm_num only [hef,heg,heh] at H
  obtain ⟨_,y',hy',_⟩ := H mh2BoundaryClass 0 0 0 sx
    (by decide) (by decide) (by decide) hx hy hxBar hyBar hsusp hh
    candidate_zero_differential (Or.inr hcross) hg
  exact nonzero_leading_image_no_positive_extension .sphere .nuCofiber
    rotatedNuRouteTriangle.f 3 1 3 17 (by decide) mh2BoundaryClass hbottom ⟨y',hy'⟩

/-- The rotated nu triangle and the boundary d₂(h₄) refute this
exact-source version of the generalized Mahowald law. -/
private theorem rotated_nu_generalized_mahowald_law_false :
    ¬GeneralizedMahowaldLaw background rotatedNuRouteTriangle := by
  apply mh2_candidate_refutation_of_bottom_nonzero
  apply zero_normalized_leading_nonzero .sphere .nuCofiber rotatedNuRouteTriangle.f
    rotated_nu_f_exponent mh2BoundaryClass
  exact nu_bottom_boundary_leading_nonzero

end
end KIP126.ProofTools.Internal.Mahowald
