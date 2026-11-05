module

import all KIP126.Literature.E2Exactness.BasisDecomposition
import all KIP126.Literature.E2Exactness.HModuleGeneratorNatural
import KIP126.AdamsSynthetic.Completed.HomotopyCoproduct

namespace KIP126.AdamsSynthetic.HModuleDecomposition
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard.HModuleGenerator
noncomputable section
set_option backward.isDefEq.respectTransparency false

private instance actualSmallCoproducts : HasCoproducts.{0} Spectrum :=
  smallSpectrumCoproducts

private theorem coefficient_tensor_homotopy_two (X : Spectrum) (d : ℤ)
    (a : HomotopyGroup d (coefficients.object ⊗ X)) : (2 : ℕ) • a = 0 := by
  have h := congrArg (fun f => a ≫ f) (coefficient_tensor_two_id_zero X)
  simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero] using h

private instance coefficientTensorHomotopyModule (X : Spectrum) (d : ℤ) :
    Module (ZMod 2) (HomotopyGroup d (coefficients.object ⊗ X)) :=
  AddCommGroup.zmodModule (coefficient_tensor_homotopy_two X d)

private def coefficientTensorBasisIndex (X : Spectrum) (d : ℤ) : Type :=
  Module.Free.ChooseBasisIndex (ZMod 2) (HomotopyGroup d (coefficients.object ⊗ X))

private def coefficientTensorBasis (X : Spectrum) (d : ℤ) :
    Module.Basis (coefficientTensorBasisIndex X d) (ZMod 2)
      (HomotopyGroup d (coefficients.object ⊗ X)) :=
  Module.Free.chooseBasis (ZMod 2) (HomotopyGroup d (coefficients.object ⊗ X))

private def coefficientTensorWedgeIndex (X : Spectrum) : Type :=
  Σ d : ℤ, coefficientTensorBasisIndex X d

private def coefficientTensorWedgeFamily (X : Spectrum)
    (j : coefficientTensorWedgeIndex X) : Spectrum := coefficients.object⟦j.1⟧

private def coefficientTensorBasisExtension (X : Spectrum)
    (j : coefficientTensorWedgeIndex X) :
    coefficientTensorWedgeFamily X j ⟶ coefficients.object ⊗ X :=
  generatorExtension X j.1 (coefficientTensorBasis X j.1 j.2)

private def coefficientTensorWedge (X : Spectrum) : Spectrum :=
  ∐ coefficientTensorWedgeFamily X

/-- The actual original coproduct descent of the canonical μ-extensions of
an F₂ basis in each homotopy degree. -/
private def coefficientTensorWedgeMap (X : Spectrum) :
    coefficientTensorWedge X ⟶ coefficients.object ⊗ X :=
  Sigma.desc (coefficientTensorBasisExtension X)

private theorem coefficientTensorWedgeMap_inclusion (X : Spectrum)
    (j : coefficientTensorWedgeIndex X) :
    Sigma.ι (coefficientTensorWedgeFamily X) j ≫ coefficientTensorWedgeMap X =
      generatorExtension X j.1 (coefficientTensorBasis X j.1 j.2) :=
  Sigma.ι_desc (coefficientTensorBasisExtension X) j

private theorem coefficientTensorBasisExtension_unit (X : Spectrum)
    (j : coefficientTensorWedgeIndex X) :
    (shiftFunctor Spectrum j.1).map coefficients.unit ≫
      coefficientTensorBasisExtension X j = coefficientTensorBasis X j.1 j.2 :=
  generatorExtension_unit X j.1 (coefficientTensorBasis X j.1 j.2)

/-- The chosen descent is bijective on every original stable homotopy group. -/
private theorem coefficientTensorWedgeMap_homotopy_bijective (X : Spectrum) (d : ℤ) :
    Function.Bijective (inducedMap (coefficientTensorWedgeMap X) d) := by
  letI := homotopy_preserves_coefficient_coproduct
    (fun j : Σ n, coefficientTensorBasisIndex X n => j.1) d
  exact basisCoproduct_inducedMap_bijective coefficients (coefficients.object ⊗ X)
    (coefficientTensorBasisIndex X) (coefficientTensorBasis X)
    (coefficientTensorBasisExtension X) (coefficientTensorBasisExtension_unit X) d

private instance coefficientTensorWedgeMap_isIso (X : Spectrum) :
    IsIso (coefficientTensorWedgeMap X) :=
  isIso_of_homotopy_bijective (coefficientTensorWedgeMap X)
    (coefficientTensorWedgeMap_homotopy_bijective X)

/-- Every actual H⊗X is the actual small coproduct of shifted actual H indexed
by chosen bases of its original stable homotopy groups. -/
private def coefficientTensorWedgeIso (X : Spectrum) :
    coefficientTensorWedge X ≅ coefficients.object ⊗ X :=
  asIso (coefficientTensorWedgeMap X)


end
end KIP126.AdamsSynthetic.HModuleDecomposition
