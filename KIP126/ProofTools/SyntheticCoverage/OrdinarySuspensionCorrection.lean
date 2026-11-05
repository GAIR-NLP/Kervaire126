module

import KIP126.AdamsSynthetic.Quotients

/-! Corrections of finite suspension comparisons.
In a stable homotopy category, an endomorphism annihilated by both structure
arrows of a distinguished cofiber triangle has square zero. This supplies
invertible corrections under the displayed linear suspension-square condition.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Triangle exactness makes an endomorphism of the third object
that annihilates both structure arrows square-zero. -/
private theorem cofiber_correction_square_zero
    (T : Triangle C) (hT : T ∈ distTriang C)
    (u : T.obj₃ ⟶ T.obj₃) (hi : T.mor₂ ≫ u = 0) (hp : u ≫ T.mor₃ = 0) :
    u ≫ u = 0 := by
  obtain ⟨z,hz⟩ := T.yoneda_exact₃ hT u hi
  calc
    u ≫ u = u ≫ (T.mor₃ ≫ z) := congrArg (fun a => u ≫ a) hz
    _ = 0 := by rw [← Category.assoc,hp,zero_comp]

private def square_zero_perturbation_iso
    {A : C} (u : A ⟶ A) (hu : u ≫ u = 0) : A ≅ A where
  hom := 𝟙 A + u
  inv := 𝟙 A - u
  hom_inv_id := by
    simp only [Preadditive.add_comp,Preadditive.comp_sub,Category.id_comp,
      Category.comp_id,hu]
    abel
  inv_hom_id := by
    simp only [Preadditive.sub_comp,Preadditive.comp_add,Category.id_comp,
      Category.comp_id,hu]
    abel

/-- A correction preserving both cofiber structure maps preserves
invertibility. Its inverse is constructed by a square-zero perturbation. -/
private theorem cofiber_corrected_comparison_exists
    (T : Triangle C) (hT : T ∈ distTriang C)
    {D : C} (e : T.obj₃ ≅ D) (p : D ⟶ T.obj₁⟦(1:ℤ)⟧)
    (he : e.hom ≫ p = T.mor₃)
    (h : T.obj₃ ⟶ D) (hi : T.mor₂ ≫ h = 0) (hp : h ≫ p = 0) :
    ∃ e' : T.obj₃ ≅ D, e'.hom = e.hom + h := by
  let u := h ≫ e.inv
  have hiu : T.mor₂ ≫ u = 0 := by
    dsimp only [u]
    rw [← Category.assoc,hi,zero_comp]
  have hup : u ≫ T.mor₃ = 0 := by
    dsimp only [u]
    rw [← he,Category.assoc,Iso.inv_hom_id_assoc,hp]
  let eu := square_zero_perturbation_iso u (cofiber_correction_square_zero T hT u hiu hup)
  refine ⟨eu ≪≫ e,?_⟩
  simp only [Iso.trans_hom,eu,square_zero_perturbation_iso,Preadditive.add_comp,
    Category.id_comp,u,Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- A left-factor defect can be removed by the same square-zero correction.
The two annihilation conditions are explicit hypotheses. -/
private theorem cofiber_comparison_of_left_defect
    (T : Triangle C) (hT : T ∈ distTriang C)
    {D E : C} (e : T.obj₃ ≅ D) (f : T.obj₃ ⟶ E) (g : D ⟶ E)
    (u : T.obj₃ ⟶ T.obj₃) (hi : T.mor₂ ≫ u = 0) (hp : u ≫ T.mor₃ = 0)
    (hdefect : e.hom ≫ g = f - u ≫ f) :
    ∃ e' : T.obj₃ ≅ D,
      T.mor₂ ≫ e'.hom = T.mor₂ ≫ e.hom ∧ e'.hom ≫ g = f := by
  have hu := cofiber_correction_square_zero T hT u hi hp
  let eu := square_zero_perturbation_iso u hu
  refine ⟨eu ≪≫ e,?_,?_⟩
  · change T.mor₂ ≫ (𝟙 _ + u) ≫ e.hom = T.mor₂ ≫ e.hom
    rw [← Category.assoc,Preadditive.comp_add,Category.comp_id,hi,add_zero]
  · change ((𝟙 _ + u) ≫ e.hom) ≫ g = f
    rw [Category.assoc,hdefect,Preadditive.add_comp,Category.id_comp,Preadditive.comp_sub,
      ← Category.assoc,hu,zero_comp]
    abel

variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- A sufficient linear correction equation for the literal suspension square. -/
private theorem suspension_square_of_cofiber_correction
    (A B : Syn) (f : A ⟶ B) (q : ℕ)
    (eA : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (B⟦(1:ℤ)⟧) q ≅ (XModLambdaN B q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl _ q ≫ eA.hom =
      (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.incl A q))
    (h : XModLambdaN (A⟦(1:ℤ)⟧) q ⟶ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (hi : XModLambdaN.incl _ q ≫ h = 0)
    (hp : h ≫ eA.inv ≫ XModLambdaN.proj _ q = 0)
    (hcorrection : h ≫ (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.map f q) =
      XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map f) q ≫ eB.hom -
        eA.hom ≫ (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.map f q)) :
    ∃ eA' : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q ≫ eA'.hom =
        (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.incl A q) ∧
      XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map f) q ≫ eB.hom =
        eA'.hom ≫ (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.map f q) := by
  obtain ⟨eA',heA'⟩ := cofiber_corrected_comparison_exists
    (XModLambdaN.cofiberTriangle (A⟦(1:ℤ)⟧) q)
    (XModLambdaN.cofiberTriangle_distinguished _ _) eA
    (eA.inv ≫ XModLambdaN.proj _ q) (by simp [XModLambdaN.cofiberTriangle]) h hi hp
  refine ⟨eA',?_,?_⟩
  · rw [heA',Preadditive.comp_add,hi,add_zero,heA]
  · rw [heA',Preadditive.add_comp,hcorrection]
    abel

end
end KIP126.ProofTools.Internal.SyntheticCoverage
