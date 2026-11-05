module

import all KIP126.ProofTools.CrossingCounterexample.Base

/-! The candidate matrix on the actual normalized finite extension map. -/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Classical.Adams
open KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def matrixSourceIso :
    (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap).obj
      background.nu background.auxiliary ≅ background.nu.functor.obj candidateSpectrum :=
  zero_positive_iso
    (background.nu.functor.obj (candidateAdamsObject.obj background.auxiliary))
    _ matrixMap_normalizedExponent

private theorem matrix_normalized_map :
    (background.normalizedMap candidateAdamsObject candidateAdamsObject matrixMap).map =
      matrixSourceIso.hom ≫ background.nu.functor.map matrixMap := by
  simpa only [matrixSourceIso, zero_positive_iso, Iso.trans_hom, eqToIso.hom,
    Iso.app_hom, Category.assoc] using
    normalized_zero_map candidateAdamsObject candidateAdamsObject matrixMap matrixMap_normalizedExponent

private def matrixFiniteSourceIso (q : ℕ) :
    (SyntheticObject.quotient q
      (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap)).obj
        background.nu background.auxiliary ≅ (quotientNu q).obj candidateSpectrum :=
  (background.quotients.functoriality.functor q).mapIso matrixSourceIso

private theorem matrix_finite_map (q : ℕ) :
    finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap q =
      (matrixFiniteSourceIso q).hom ≫ (quotientNu q).map matrixMap := by
  change XModLambdaN.map _ q = _
  rw [matrix_normalized_map, background.quotients.functoriality.map_comp]
  rfl

private abbrev matrixCoordinates (q : ℕ) :=
  (quotientNu q).obj S ⊞ ((quotientNu q).obj mooreFour ⊞ (quotientNu q).obj S)

private def matrixFiniteCoordinates (q : ℕ) (hq : 0 < q) :
    (SyntheticObject.quotient q
      (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap)).obj
        background.nu background.auxiliary ≅ matrixCoordinates q :=
  matrixFiniteSourceIso q ≪≫ candidateQuotientBiprodIso q hq

private def matrixInCoordinates (q : ℕ) : matrixCoordinates q ⟶ matrixCoordinates q :=
  biprod.lift (biprod.snd ≫ biprod.snd ≫ ((4 : ℕ) • 𝟙 ((quotientNu q).obj S)))
    (biprod.lift (biprod.fst ≫ (quotientNu q).map bottom)
      (biprod.fst ≫ ((2 : ℕ) • 𝟙 ((quotientNu q).obj S))))

private theorem matrix_finite_coordinates (q : ℕ) (hq : 0 < q) :
    (matrixFiniteCoordinates q hq).inv ≫
      finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap q ≫
        (candidateQuotientBiprodIso q hq).hom = matrixInCoordinates q := by
  rw [matrix_finite_map]
  simp only [matrixFiniteCoordinates, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact candidateQuotient_matrix q hq

private theorem matrix_image (q : ℕ) (hq : 0 < q) (m w : ℤ)
    (a : BiHom m w ((quotientNu q).obj S))
    (b : BiHom m w ((quotientNu q).obj mooreFour))
    (c : BiHom m w ((quotientNu q).obj S)) :
    (biprod.lift a (biprod.lift b c) ≫ (matrixFiniteCoordinates q hq).inv) ≫
        finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap q ≫
          (candidateQuotientBiprodIso q hq).hom =
      biprod.lift ((4 : ℕ) • c)
        (biprod.lift (a ≫ (quotientNu q).map bottom) ((2 : ℕ) • a)) := by
  rw [Category.assoc, matrix_finite_coordinates]
  apply biprod.hom_ext
  · simp [matrixInCoordinates, Category.assoc, Preadditive.comp_nsmul]
  · apply biprod.hom_ext <;>
      simp [matrixInCoordinates, Category.assoc, Preadditive.comp_nsmul]

end
end KIP126.ProofTools.Internal.CrossingCounterexample
