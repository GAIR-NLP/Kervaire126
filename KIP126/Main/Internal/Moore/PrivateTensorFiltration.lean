module

import KIP126.Literature.Standard.QuotientAlgebra

/-! Tensoring preserves the coefficient-unit Adams filtration.
Exactness constructs the tower-stage maps using the same unit
on both towers. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem tensor_unit_natural {H X Y : SyntheticSpectrum}
    (unit : SphereSpectrum ⟶ H) (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv ≫ unit ▷ Y =
      (λ_ X).inv ≫ unit ▷ X ≫ H ◁ f := by
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange]

private theorem tensor_right_unit {H : SyntheticSpectrum}
    (unit : SphereSpectrum ⟶ H) (Y A : SyntheticSpectrum) :
    (λ_ (Y ⊗ A)).inv ≫ unit ▷ (Y ⊗ A) =
      (((λ_ Y).inv ≫ unit ▷ Y) ▷ A) ≫ (α_ H Y A).hom := by
  rw [leftUnitor_tensor_inv, comp_whiskerRight]
  simp only [Category.assoc]
  rw [associator_naturality_left]

private theorem tensor_right_tower_lift {H : SyntheticSpectrum}
    {unit : SphereSpectrum ⟶ H} {X : SyntheticSpectrum} (A : SyntheticSpectrum)
    (T : AbstractAdamsTower unit X) (U : AbstractAdamsTower unit (X ⊗ A)) :
    ∀ n : ℕ, ∃ c : T.stage n ⊗ A ⟶ U.stage n,
      c ≫ U.projection (n : ℤ) = T.projection (n : ℤ) ▷ A := by
  letI := KIP126.Literature.Standard.mayData.rightShift A
  letI := KIP126.Literature.Standard.mayData.rightExact A
  intro n
  induction n with
  | zero =>
    refine ⟨(T.zeroIso.hom ▷ A) ≫ U.zeroIso.inv, ?_⟩
    have hT : T.projection 0 = T.zeroIso.hom := by
      simp only [AbstractAdamsTower.projection, AbstractAdamsTower.map_self]
      exact Category.id_comp _
    have hU : U.projection 0 = U.zeroIso.hom := by
      simp only [AbstractAdamsTower.projection, AbstractAdamsTower.map_self]
      exact Category.id_comp _
    change (T.zeroIso.hom ▷ A ≫ U.zeroIso.inv) ≫ U.projection 0 = T.projection 0 ▷ A
    rw [hT, hU, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    let a : T.stage (n + 1) ⊗ A ⟶ U.stage n := (T.map (Nat.le_succ n) ▷ A) ≫ c
    have hz : a ≫ HasFunctorialCofiber.cofibι (U.map (Nat.le_succ n)) = 0 := by
      apply (cancel_mono (U.layerIso n).hom).mp
      rw [Category.assoc, U.layer_unit]
      dsimp only [a]
      rw [Category.assoc, tensor_unit_natural, reassoc_of% tensor_right_unit unit (T.stage n) A]
      rw [←comp_whiskerRight_assoc]
      have hzero : T.map (Nat.le_succ n) ≫
          ((λ_ (T.stage n)).inv ≫ unit ▷ T.stage n) = 0 := by
        rw [←T.layer_unit, ←Category.assoc]
        have h : T.map (Nat.le_succ n) ≫ HasFunctorialCofiber.cofibι (T.map (Nat.le_succ n)) = 0 :=
          comp_distTriang_mor_zero₁₂ _
            (HasFunctorialCofiber.cofib_distinguished (T.map (Nat.le_succ n)))
        rw [h, zero_comp]
      rw [hzero]
      have hzeroA : (0 : T.stage (n + 1) ⟶ H ⊗ T.stage n) ▷ A = 0 :=
        (tensorRight A).map_zero _ _
      simp only [hzeroA, zero_comp]
    obtain ⟨c', hc'⟩ := Triangle.coyoneda_exact₂
      _ (HasFunctorialCofiber.cofib_distinguished (U.map (Nat.le_succ n))) a hz
    change a = c' ≫ U.map (Nat.le_succ n) at hc'
    refine ⟨c', ?_⟩
    have hU : U.map (Nat.le_succ n) ≫ U.projection (n : ℤ) =
        U.projection ((n + 1 : ℕ) : ℤ) :=
      U.projection_compat (show (n : ℤ) ≤ ((n + 1 : ℕ) : ℤ) by omega)
    have hT : T.map (Nat.le_succ n) ≫ T.projection (n : ℤ) =
        T.projection ((n + 1 : ℕ) : ℤ) :=
      T.projection_compat (show (n : ℤ) ≤ ((n + 1 : ℕ) : ℤ) by omega)
    calc
      c' ≫ U.projection ((n + 1 : ℕ) : ℤ) =
          (c' ≫ U.map (Nat.le_succ n)) ≫ U.projection (n : ℤ) := by
        rw [Category.assoc, hU]
      _ = a ≫ U.projection (n : ℤ) := by rw [←hc']
      _ = T.projection ((n + 1 : ℕ) : ℤ) ▷ A := by
        dsimp only [a]
        rw [Category.assoc, hc, ←comp_whiskerRight, hT]

private theorem tensor_right_factor_through_projection
    {H : SyntheticSpectrum} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily SyntheticSpectrum}
    (P : SyntheticTowerPresentation unit F) {B X : SyntheticSpectrum}
    (A : SyntheticSpectrum) (s : ℤ) (f : B ⟶ X)
    (hf : ∃ g : B ⟶ (P.tower X).stageAt s, g ≫ (P.tower X).projection s = f) :
    ∃ g : B ⊗ A ⟶ (P.tower (X ⊗ A)).stageAt s,
      g ≫ (P.tower (X ⊗ A)).projection s = f ▷ A := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨c, hc⟩ := tensor_right_tower_lift A (P.tower X) (P.tower (X ⊗ A)) s.toNat
  have hp (Y : SyntheticSpectrum) :
      (P.tower Y).projection (s.toNat : ℤ) = (P.tower Y).projection s := by
    simp only [AbstractAdamsTower.projection, Int.toNat_natCast]
  rw [hp, hp] at hc
  refine ⟨(g ▷ A) ≫ c, ?_⟩
  rw [Category.assoc, hc, ←comp_whiskerRight, hg]

private theorem tensor_right_filtration
    {H : SyntheticSpectrum} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily SyntheticSpectrum}
    (P : SyntheticTowerPresentation unit F) {X : SyntheticSpectrum}
    (A : SyntheticSpectrum) (s m w m' w' : ℤ) (f : BiHom m w X)
    (hf : FiltrationAtLeast P s f) (d : Smn m' w' ⟶ Smn m w ⊗ A) :
    FiltrationAtLeast P s (d ≫ (f ▷ A)) := by
  obtain ⟨g, hg⟩ := tensor_right_factor_through_projection P A s f hf
  refine ⟨d ≫ g, ?_⟩
  change (d ≫ g) ≫ (P.tower (X ⊗ A)).projection s = d ≫ (f ▷ A)
  rw [Category.assoc, hg]

private theorem tensor_left_factor_through_projection
    {H : SyntheticSpectrum} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily SyntheticSpectrum}
    (P : SyntheticTowerPresentation unit F) {B X : SyntheticSpectrum}
    (A : SyntheticSpectrum) (s : ℤ) (f : B ⟶ X)
    (hf : ∃ g : B ⟶ (P.tower X).stageAt s, g ≫ (P.tower X).projection s = f) :
    ∃ g : A ⊗ B ⟶ (P.tower (A ⊗ X)).stageAt s,
      g ≫ (P.tower (A ⊗ X)).projection s = A ◁ f := by
  letI := KIP126.Literature.Standard.quotientSyntheticSymmetric
  obtain ⟨g, hg⟩ := tensor_right_factor_through_projection P A s f hf
  let φ := P.map (β_ X A).hom
  refine ⟨(β_ A B).hom ≫ g ≫ φ.stage s.toNat, ?_⟩
  simp only [Category.assoc]
  rw [φ.projection, ←Category.assoc g, hg]
  rw [BraidedCategory.braiding_naturality_left, ←Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]

private theorem tensor_left_filtration
    {H : SyntheticSpectrum} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily SyntheticSpectrum}
    (P : SyntheticTowerPresentation unit F) {X : SyntheticSpectrum}
    (A : SyntheticSpectrum) (s m w m' w' : ℤ) (f : BiHom m w X)
    (hf : FiltrationAtLeast P s f) (d : Smn m' w' ⟶ A ⊗ Smn m w) :
    FiltrationAtLeast P s (d ≫ (A ◁ f)) := by
  obtain ⟨g, hg⟩ := tensor_left_factor_through_projection P A s f hf
  refine ⟨d ≫ g, ?_⟩
  change (d ≫ g) ≫ (P.tower (A ⊗ X)).projection s = d ≫ (A ◁ f)
  rw [Category.assoc, hg]

end
end KIP126.Main.Internal.Moore
