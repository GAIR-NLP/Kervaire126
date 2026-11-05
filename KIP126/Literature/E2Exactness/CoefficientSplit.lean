module
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import KIP126.AdamsSynthetic.Background
import KIP126.AdamsSynthetic.Tower
import KIP126.AdamsSynthetic.AdamsFiltration

@[expose] section
namespace HModuleSplit
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open CategoryTheory.Pretriangulated
noncomputable section
set_option autoImplicit false
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual left coefficient unit; all maps remain in the original category. -/
private def eta (H X : C) (unit : 𝟙_ C ⟶ H) : X ⟶ H ⊗ X :=
  (λ_ X).inv ≫ unit ▷ X

private theorem unit_precomposition_agrees (H : C) (u : 𝟙_ C ⟶ H) :
    u ≫ (ρ_ H).inv ≫ H ◁ u = u ≫ (λ_ H).inv ≫ u ▷ H := by
  calc
    u ≫ (ρ_ H).inv ≫ H ◁ u = (ρ_ (𝟙_ C)).inv ≫ (u ⊗ₘ u) :=
      (rightUnitor_inv_comp_tensorHom u u).symm
    _ = (λ_ (𝟙_ C)).inv ≫ (u ⊗ₘ u) := by rw [unitors_inv_equal]
    _ = u ≫ (λ_ H).inv ≫ u ▷ H := leftUnitor_inv_comp_tensorHom u u

private theorem right_unit_of_left_unit_and_detection
    (H : C) (u : 𝟙_ C ⟶ H) (μ : H ⊗ H ⟶ H)
    (hleft : ((λ_ H).inv ≫ u ▷ H) ≫ μ = 𝟙 H)
    (hu : ∀ f g : H ⟶ H, u ≫ f = u ≫ g → f = g) :
    ((ρ_ H).inv ≫ H ◁ u) ≫ μ = 𝟙 H := by
  apply hu
  calc
    u ≫ (((ρ_ H).inv ≫ H ◁ u) ≫ μ) =
        (u ≫ (ρ_ H).inv ≫ H ◁ u) ≫ μ := by simp only [Category.assoc]
    _ = (u ≫ (λ_ H).inv ≫ u ▷ H) ≫ μ := by rw [unit_precomposition_agrees]
    _ = u ≫ (((λ_ H).inv ≫ u ▷ H) ≫ μ) := by simp only [Category.assoc]
    _ = u ≫ 𝟙 H := by rw [hleft]

/-- A left-unital multiplication splits the actual unit on every coefficient tensor. -/
private theorem eta_tensor_split (H X : C) (unit : 𝟙_ C ⟶ H)
    (mul : H ⊗ H ⟶ H) (hleft : eta H H unit ≫ mul = 𝟙 H) :
    eta H (H ⊗ X) unit ≫ (α_ H H X).inv ≫ mul ▷ X = 𝟙 (H ⊗ X) := by
  dsimp only [eta] at hleft ⊢
  rw [Category.assoc] at hleft
  rw [Category.assoc, associator_inv_naturality_left_assoc]
  rw [← leftUnitor_inv_whiskerRight_assoc, ← comp_whiskerRight,
    ← comp_whiskerRight, hleft, id_whiskerRight]

/-- A right-unital multiplication splits H smashed with the actual unit of X. -/
private theorem tensor_eta_split (H X : C) (unit : 𝟙_ C ⟶ H)
    (mul : H ⊗ H ⟶ H)
    (hright : ((ρ_ H).inv ≫ H ◁ unit) ≫ mul = 𝟙 H) :
    H ◁ eta H X unit ≫ (α_ H H X).inv ≫ mul ▷ X = 𝟙 (H ⊗ X) := by
  dsimp only [eta]
  rw [Category.assoc] at hright
  rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_middle_assoc]
  rw [← Category.assoc, triangle_assoc_comp_left_inv]
  rw [← comp_whiskerRight, ← comp_whiskerRight, hright, id_whiskerRight]

/-- Naturality of the coefficient unit. -/
private theorem eta_naturality (H : C) (unit : 𝟙_ C ⟶ H)
    {X Y : C} (f : X ⟶ Y) :
    eta H X unit ≫ H ◁ f = f ≫ eta H Y unit := by
  dsimp only [eta]
  simpa only [Category.assoc, tensorHom_def] using leftUnitor_inv_comp_tensorHom unit f

/-- Every map into H⊗Y extends over the actual coefficient unit of its source. -/
private theorem coefficient_tensor_factor (H Y : C) (unit : 𝟙_ C ⟶ H)
    (mul : H ⊗ H ⟶ H) (hleft : eta H H unit ≫ mul = 𝟙 H)
    {X : C} (f : X ⟶ H ⊗ Y) :
    eta H X unit ≫ H ◁ f ≫ (α_ H H Y).inv ≫ mul ▷ Y = f := by
  rw [← Category.assoc (eta H X unit), eta_naturality]
  simp only [Category.assoc]
  rw [eta_tensor_split H Y unit mul hleft, Category.comp_id]

section Zero
variable [HasZeroMorphisms C]

private theorem tensor_zero_of_unit_zero (H : C) (unit : 𝟙_ C ⟶ H)
    (mul : H ⊗ H ⟶ H)
    (hright : ((ρ_ H).inv ≫ H ◁ unit) ≫ mul = 𝟙 H)
    [(tensorLeft H).PreservesZeroMorphisms]
    {X Y : C} (f : X ⟶ Y) (hf : f ≫ eta H Y unit = 0) : H ◁ f = 0 := by
  calc
    H ◁ f = H ◁ f ≫ (H ◁ eta H Y unit ≫ (α_ H H Y).inv ≫ mul ▷ Y) := by
      rw [tensor_eta_split H Y unit mul hright, Category.comp_id]
    _ = H ◁ (f ≫ eta H Y unit) ≫ (α_ H H Y).inv ≫ mul ▷ Y := by
      rw [whiskerLeft_comp, Category.assoc]
    _ = 0 := by
      rw [hf]
      change (tensorLeft H).map (0 : X ⟶ H ⊗ Y) ≫ _ = 0
      rw [Functor.map_zero, zero_comp]

/-- Actual H-null maps annihilate all maps into a coefficient tensor. -/
private theorem coefficient_tensor_annihilates (H Y : C) (unit : 𝟙_ C ⟶ H)
    (mul : H ⊗ H ⟶ H) (hleft : eta H H unit ≫ mul = 𝟙 H)
    {A X : C} (f : A ⟶ X) (hf : H ◁ f = 0) (g : X ⟶ H ⊗ Y) : f ≫ g = 0 := by
  rw [← coefficient_tensor_factor H Y unit mul hleft g]
  rw [← Category.assoc f, ← eta_naturality]
  simp only [hf, zero_comp, comp_zero]
end Zero

section Stable
open KIP126.StableHomotopy KIP126.AdamsSynthetic
variable {D : Type u} [StableHomotopyCategory.{u, v} D]
  [HasFunctorialCofiber (C := D)]

/-- For the actual unit fiber tower, every adjacent map is killed by H tensor.
The displayed tensor background, tower, multiplication and right unit law
are retained as explicit inputs; the tower cofiber equations are used verbatim. -/
private theorem adams_step_tensor_zero (B : ClosedSymmetricTensorTriangulated D)
    (H : D) (unit : SphereSpectrum ⟶ H) (mul : H ⊗ H ⟶ H)
    (hright : ((ρ_ H).inv ≫ H ◁ unit) ≫ mul = 𝟙 H)
    {X : D} (T : AbstractAdamsTower unit X) (s : ℕ) :
    H ◁ T.map (Nat.le_succ s) = 0 := by
  letI := B.symmetric
  letI := B.tensorShift H
  letI := B.tensorExact H
  letI : (tensorLeft H).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso (tensorLeftIsoTensorRight H).symm
  apply tensor_zero_of_unit_zero H unit mul hright
  dsimp only [eta]
  rw [← T.layer_unit s, ← Category.assoc]
  have hz := comp_distTriang_mor_zero₁₂
    (Triangle.mk (T.map (Nat.le_succ s)) _ _)
    (HasFunctorialCofiber.cofib_distinguished (T.map (Nat.le_succ s)))
  change T.map (Nat.le_succ s) ≫ HasFunctorialCofiber.cofibι _ = 0 at hz
  rw [hz, zero_comp]

/-- The same adjacent maps vanish under the repository's actual homology map. -/
private theorem adams_step_homology_zero (B : ClosedSymmetricTensorTriangulated D)
    (H : ModTwoCoefficients D) (mul : H.object ⊗ H.object ⟶ H.object)
    (hright : ((ρ_ H.object).inv ≫ H.object ◁ H.unit) ≫ mul = 𝟙 H.object)
    {X : D} (T : AbstractAdamsTower H.unit X) (s : ℕ) :
    ZeroOnModTwoHomology H (T.map (Nat.le_succ s)) := by
  intro n x
  change x ≫ H.object ◁ T.map (Nat.le_succ s) = 0
  rw [adams_step_tensor_zero B H.object H.unit mul hright T s, comp_zero]

omit [HasFunctorialCofiber (C := D)] in
/-- Hom exactness gives extensions into H⊗Y across a triangle
whose first morphism is killed by H tensor. -/
private theorem coefficient_tensor_extension (H Y : D) (unit : SphereSpectrum ⟶ H)
    (mul : H ⊗ H ⟶ H) (hleft : eta H H unit ≫ mul = 𝟙 H)
    (T : Triangle D) (hT : T ∈ distTriang D) (hz : H ◁ T.mor₁ = 0)
    (g : T.obj₂ ⟶ H ⊗ Y) :
    ∃ lift : T.obj₃ ⟶ H ⊗ Y, T.mor₂ ≫ lift = g := by
  obtain ⟨lift, hlift⟩ := T.yoneda_exact₂ hT g
    (coefficient_tensor_annihilates H Y unit mul hleft T.mor₁ hz g)
  exact ⟨lift, hlift.symm⟩
end Stable

end
end HModuleSplit
