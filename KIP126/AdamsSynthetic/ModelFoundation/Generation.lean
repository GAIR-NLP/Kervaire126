module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.SmallObject.Basic

/-! Cofibrantly generated model foundations, independent of a chosen homotopy category or triangulation. The small
object argument constructs functorial factorizations on the actual point-set arrow category. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v

/-- Generating classes for the supplied model structure, including the
smallness hypotheses used for functorial replacement. -/
public structure CofibrantGeneration (P : Type u)
    [Category.{v} P] [ModelCategory P] where
  generatingCofibrations : MorphismProperty P
  generatingTrivialCofibrations : MorphismProperty P
  cofibrationsRlp : generatingCofibrations.rlp = trivialFibrations P
  trivialCofibrationsRlp : generatingTrivialCofibrations.rlp = fibrations P
  cofibrationsSmall : MorphismProperty.HasSmallObjectArgument.{u} generatingCofibrations
  trivialCofibrationsSmall :
    MorphismProperty.HasSmallObjectArgument.{u} generatingTrivialCofibrations

namespace CofibrantGeneration
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (G : CofibrantGeneration C)

/-- A cofibrantly generated model category has functorial cofibration--trivial
fibration factorizations. -/
public noncomputable def cofibrationTrivialFibrationFactorization :
    MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C) := by
  letI := G.cofibrationsSmall
  have hleft : G.generatingCofibrations.rlp.llp = cofibrations C := by
    rw [G.cofibrationsRlp]
    exact MorphismProperty.llp_eq_of_wfs _ _
  rw [← hleft, ← G.cofibrationsRlp]
  exact MorphismProperty.functorialFactorizationData
    G.generatingCofibrations.rlp.llp G.generatingCofibrations.rlp

/-- A cofibrantly generated model category has functorial trivial
cofibration--fibration factorizations. -/
public noncomputable def trivialCofibrationFibrationFactorization :
    MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C) := by
  letI := G.trivialCofibrationsSmall
  have hleft : G.generatingTrivialCofibrations.rlp.llp =
      trivialCofibrations C := by
    rw [G.trivialCofibrationsRlp]
    exact MorphismProperty.llp_eq_of_wfs _ _
  rw [← hleft, ← G.trivialCofibrationsRlp]
  exact MorphismProperty.functorialFactorizationData
    G.generatingTrivialCofibrations.rlp.llp G.generatingTrivialCofibrations.rlp

/-- The functorial cofibrant replacement obtained by factoring every map from
 the initial object as a cofibration followed by a trivial fibration. -/
public noncomputable def cofibrantReplacementFunctor : C ⥤ C where
  obj X := G.cofibrationTrivialFibrationFactorization.Z.obj
    (Arrow.mk (initial.to X))
  map {X Y} f := G.cofibrationTrivialFibrationFactorization.Z.map
    (Arrow.homMk (𝟙 (⊥_ C)) f (by simp))
  map_id X := by
    rw [← G.cofibrationTrivialFibrationFactorization.Z.map_id]
    congr 1
  map_comp f g := by
    rw [← G.cofibrationTrivialFibrationFactorization.Z.map_comp]
    congr 1
    ext <;> simp

/-- The natural trivial fibration from the functorial cofibrant replacement
 to the identity functor. -/
public noncomputable def cofibrantReplacementCounit :
    G.cofibrantReplacementFunctor ⟶ 𝟭 C where
  app X := G.cofibrationTrivialFibrationFactorization.p.app
    (Arrow.mk (initial.to X))
  naturality X Y f := by
    exact G.cofibrationTrivialFibrationFactorization.p.naturality
      (Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Y))
        (𝟙 (⊥_ C)) f (by simp))

/-- Every value of the functorial replacement is cofibrant. -/
public theorem cofibrantReplacement_isCofibrant (X : C) :
    IsCofibrant (G.cofibrantReplacementFunctor.obj X) := by
  exact (isCofibrant_iff_of_isInitial
    (G.cofibrationTrivialFibrationFactorization.i.app
      (Arrow.mk (initial.to X))) initialIsInitial).2
    ((cofibration_iff _).2
      (G.cofibrationTrivialFibrationFactorization.hi
        (Arrow.mk (initial.to X))))

/-- The replacement counit is a weak equivalence. -/
public theorem cofibrantReplacementCounit_weakEquivalence (X : C) :
    weakEquivalences C (G.cofibrantReplacementCounit.app X) :=
  (G.cofibrationTrivialFibrationFactorization.hp
    (Arrow.mk (initial.to X))).2


end CofibrantGeneration
end KIP126.StableHomotopy
