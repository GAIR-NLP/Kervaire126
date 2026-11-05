module

public import KIP126.Main.SectionSeven.Predicates

/-! The ν-bottom equations for the specified Cν triangle.
Its zero composites and λν multiple equation use the same selected maps. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def hopfNu : BiHom 3 4 (S_0_0 : SyntheticSpectrum) :=
  normalizedNu background Standard.nuCofiber_nu_exponent

private def nuBottom : (S_0_0 : SyntheticSpectrum) ⟶
    background.nu.functor.obj (HasFunctorialCofiber.cofib background.auxiliary.nuMap) :=
  background.nu.unitIso.inv ≫
    background.nu.functor.map (HasFunctorialCofiber.cofibι background.auxiliary.nuMap)

private def negativeZeroIso (k : ℕ) (hk : k = 0) (X : SyntheticSpectrum) :
    (SyntheticCategory.biShift (0,-(k:ℤ))).obj X ≅ X := by
  subst k
  exact SyntheticCategory.biShift_zero.app X

private theorem negative_lift_zero_factorization {X Y : SyntheticSpectrum}
    (k : ℕ) (hk : k=0)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj X ⟶ Y)
    (g : X ⟶ Y) (h : lambdaToPositivePow k X ≫ f = g) :
    negativeLift k f ≫ (negativeZeroIso k hk Y).hom = g := by
  subst k
  rw [← h]
  dsimp only [negativeLift, negativeZeroIso, lambdaToPositivePow, lambdaPow]
  simp only [eqToHom_refl, Category.id_comp, Iso.app_hom, Category.assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality]
  rfl

private theorem normalized_nu_bottom_zero : hopfNu ≫ nuBottom = 0 := by
  have hz := comp_distTriang_mor_zero₁₂ _
    (Standard.nuCofiber_triangle Standard.nuCofiber_exponent_sum)
  change (background.normalizedMap (.shift 3 .sphere) .sphere background.auxiliary.nuMap).map ≫
    negativeLift (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g)
      (background.normalizedMap .sphere .nuCofiber background.auxiliary.nuRouteTriangle.g).map = 0 at hz
  have hb := negative_lift_zero_factorization
    (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g)
    Standard.nuCofiber_bottom_exponent
    (background.normalizedMap .sphere .nuCofiber background.auxiliary.nuRouteTriangle.g).map
    (background.nu.functor.map background.auxiliary.nuRouteTriangle.g)
    (background.normalizedMap .sphere .nuCofiber background.auxiliary.nuRouteTriangle.g).factorization
  have hzero : (background.normalizedMap (.shift 3 .sphere) .sphere background.auxiliary.nuMap).map ≫
      background.nu.functor.map (HasFunctorialCofiber.cofibι background.auxiliary.nuMap) = 0 := by
    erw [← hb, ← Category.assoc, hz, zero_comp]
  dsimp only [hopfNu, normalizedNu, nuBottom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hzero, comp_zero]

private theorem lambda_nu_multiple_bottom_zero
    (a : BiHom 122 132 (S_0_0 : SyntheticSpectrum)) :
    sphereProduct (lambdaMultiply 1 hopfNu) a ≫ nuBottom = 0 := by
  have hlam : lambdaMultiply 1 hopfNu ≫ nuBottom = 0 := by
    dsimp only [lambdaMultiply]
    simp only [Category.assoc]
    rw [normalized_nu_bottom_zero, comp_zero, comp_zero, comp_zero]
  have hc := background.sphereProductCommutative 3 3 122 132 (lambdaMultiply 1 hopfNu) a
  norm_num [homotopyRegrade] at hc
  rw [hc]
  dsimp only [sphereProduct]
  simp only [Category.assoc, hlam, comp_zero]

end
end KIP126.Main.SectionSeven
