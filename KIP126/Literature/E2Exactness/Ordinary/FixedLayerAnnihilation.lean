module
import all KIP126.Literature.E2Exactness.Ordinary.TensorStageHomology
import all KIP126.Literature.E2Exactness.Ordinary.E2MapComparison

@[expose] section
namespace KIP126.Literature.Standard.FixedLayerAnnihilation
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard.E2LayerSES KIP126.Literature.Standard.E2MapComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem coefficientTensor_left_annihilates (A : Spectrum)
    {X Y : Spectrum} (f : X ⟶ Y) (hf : coefficients.object ◁ f = 0) :
    (coefficients.object ⊗ A) ◁ f = 0 := by
  apply (cancel_mono (α_ coefficients.object A Y).hom).mp
  rw [associator_naturality_right, zero_comp,
    tensor_left_preserves_coefficient_annihilation A f hf, comp_zero]

private theorem iso_left_annihilates {A B X Y : Spectrum} (e : A ≅ B)
    (f : X ⟶ Y) (hf : B ◁ f = 0) : A ◁ f = 0 := by
  apply (cancel_mono (e.hom ▷ Y)).mp
  rw [whisker_exchange, zero_comp, hf, comp_zero]

/-- Every integer shift of a tower layer annihilates f whenever H ⊗ f
vanishes. -/
private theorem shifted_layer_tensor_annihilates {X₀ X Y : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X₀) (s n : ℤ)
    (f : X ⟶ Y) (hf : coefficients.object ◁ f = 0) :
    (T.layer s)⟦n⟧ ◁ f = 0 := by
  by_cases hs : 0 ≤ s
  · lift s to ℕ using hs
    let e : (T.layer (s : ℤ))⟦n⟧ ≅ coefficients.object ⊗ (T.stage s)⟦n⟧ :=
      (shiftFunctor Spectrum n).mapIso (T.layerIso s) ≪≫ coefficientShiftIso (T.stage s) n
    exact iso_left_annihilates e f (coefficientTensor_left_annihilates _ f hf)
  · have hz : IsZero ((T.layer s)⟦n⟧) :=
      (shiftFunctor Spectrum n).map_isZero (layer_negative_isZero T s (by omega))
    letI := closedBackground.tensorShift X
    letI := closedBackground.tensorExact X
    have hzx : IsZero ((T.layer s)⟦n⟧ ⊗ X) := (tensorRight X).map_isZero hz
    exact hzx.eq_of_src _ _

end
end KIP126.Literature.Standard.FixedLayerAnnihilation
end
