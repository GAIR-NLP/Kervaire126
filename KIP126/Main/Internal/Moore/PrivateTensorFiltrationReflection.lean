module

import all KIP126.Main.Internal.Moore.PrivateTensorFiltration

/-! Tensoring with a bigraded sphere reflects Adams filtration.
The sphere’s objectwise tensor presentation constructs the inverse;
the associator and unitors compare the inverse tensor functor naturally
with the identity. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic.Completed (SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem tensor_left_factor_through_projection_of_inverse
    {H : SyntheticSpectrum} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily SyntheticSpectrum}
    (P : SyntheticTowerPresentation unit F) {B X : SyntheticSpectrum}
    (A A' : SyntheticSpectrum) (e : A' ⊗ A ≅ (𝟙_ SyntheticSpectrum))
    (s : ℤ) (f : B ⟶ X)
    (hf : ∃ g : A ⊗ B ⟶ (P.tower (A ⊗ X)).stageAt s,
      g ≫ (P.tower (A ⊗ X)).projection s = A ◁ f) :
    ∃ g : B ⟶ (P.tower X).stageAt s,
      g ≫ (P.tower X).projection s = f := by
  let E : tensorLeft A ⋙ tensorLeft A' ≅ 𝟭 SyntheticSpectrum :=
    (tensorLeftTensor A' A).symm ≪≫
      (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
  obtain ⟨g, hg⟩ := tensor_left_factor_through_projection P A' s (A ◁ f) hf
  let φ := P.map (E.hom.app X)
  have hφ : φ.stage s.toNat ≫ (P.tower X).projection s =
      (P.tower (A' ⊗ (A ⊗ X))).projection s ≫ E.hom.app X := φ.projection s
  refine ⟨E.inv.app B ≫ g ≫ φ.stage s.toNat, ?_⟩
  simp only [Category.assoc]
  rw [hφ, ←Category.assoc g, hg]
  have hn : (A' ◁ (A ◁ f)) ≫ E.hom.app X = E.hom.app B ≫ f :=
    E.hom.naturality f
  rw [hn, ←Category.assoc, Iso.inv_hom_id_app]
  exact Category.id_comp f

private def sphereTensorInverseIso (m w : ℤ) :
    Smn (Syn := SyntheticSpectrum) (-m) (-w) ⊗ Smn m w ≅ (𝟙_ SyntheticSpectrum) :=
  (biShift_eq_tensor_Smn (-m) (-w) (Smn m w)).symm ≪≫
    (SyntheticCategory.biShift_comp (m,w) (-m,-w)).app (S_0_0 : SyntheticSpectrum) ≪≫
      eqToIso (by simp [S_0_0]) ≪≫
        SyntheticCategory.biShift_zero.app (S_0_0 : SyntheticSpectrum)

private theorem tensor_left_sphere_factor_through_projection_iff
    {H : SyntheticSpectrum} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily SyntheticSpectrum}
    (P : SyntheticTowerPresentation unit F) (m w s : ℤ) {B X : SyntheticSpectrum}
    (f : B ⟶ X) :
    (∃ g : Smn m w ⊗ B ⟶ (P.tower (Smn m w ⊗ X)).stageAt s,
      g ≫ (P.tower (Smn m w ⊗ X)).projection s = Smn m w ◁ f) ↔
    (∃ g : B ⟶ (P.tower X).stageAt s,
      g ≫ (P.tower X).projection s = f) := by
  constructor
  · exact tensor_left_factor_through_projection_of_inverse P
      (Smn m w) (Smn (-m) (-w)) (sphereTensorInverseIso m w) s f
  · exact tensor_left_factor_through_projection P (Smn m w) s f

private theorem tensor_left_sphere_filtration_iff
    {H : SyntheticSpectrum} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily SyntheticSpectrum}
    (P : SyntheticTowerPresentation unit F) {X : SyntheticSpectrum}
    (k l s m w m' w' : ℤ) (f : BiHom m w X)
    (d : Smn m' w' ≅ Smn k l ⊗ Smn m w) :
    FiltrationAtLeast P s (d.hom ≫ (Smn k l ◁ f)) ↔ FiltrationAtLeast P s f := by
  constructor
  · rintro ⟨g, hg⟩
    change g ≫ (P.tower (Smn k l ⊗ X)).projection s = d.hom ≫ (Smn k l ◁ f) at hg
    apply (tensor_left_sphere_factor_through_projection_iff P k l s f).mp
    refine ⟨d.inv ≫ g, ?_⟩
    rw [Category.assoc, hg, ←Category.assoc, d.inv_hom_id, Category.id_comp]
  · intro hf
    exact tensor_left_filtration P (Smn k l) s m w m' w' f hf d.hom

end
end KIP126.Main.Internal.Moore
