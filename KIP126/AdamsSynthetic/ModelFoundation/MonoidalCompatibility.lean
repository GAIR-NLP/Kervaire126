module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-! The primitive compatibility conditions between a model structure and its
point-set tensor. This record is independent of a homotopy-category realization. -/

@[expose] section
namespace KIP126.StableHomotopy
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
universe u v

/-- The pushout-product and unit conditions for the same point-set tensor
and model structure. The monoidal unit need not itself be cofibrant. -/
public structure MonoidalModelCompatibility (P : Type u)
    [Category.{v} P] [ModelCategory P] [MonoidalCategory P] where
  pushoutProduct : ∀ {A B X Y : P} (f : A ⟶ B) (g : X ⟶ Y),
    cofibrations P f → cofibrations P g →
    cofibrations P (MonoidalCategory.Arrow.pushoutProduct.obj
      (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  pushoutProductTrivialLeft : ∀ {A B X Y : P} (f : A ⟶ B) (g : X ⟶ Y),
    trivialCofibrations P f → cofibrations P g →
    trivialCofibrations P (MonoidalCategory.Arrow.pushoutProduct.obj
      (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  pushoutProductTrivialRight : ∀ {A B X Y : P} (f : A ⟶ B) (g : X ⟶ Y),
    cofibrations P f → trivialCofibrations P g →
    trivialCofibrations P (MonoidalCategory.Arrow.pushoutProduct.obj
      (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  unit : ∀ {QI : P} (q : QI ⟶ 𝟙_ P),
    IsCofibrant QI → weakEquivalences P q →
    ∀ X : P, IsCofibrant X → weakEquivalences P (q ▷ X)


end KIP126.StableHomotopy
end
