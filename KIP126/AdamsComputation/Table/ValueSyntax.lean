module

public import KIP126.AdamsComputation.Source

/-! Sphere-expression syntax and basis addresses using the source labels. -/

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.AdamsSynthetic.Completed
noncomputable section

public inductive Expression where
  | one
  | named (a : Atom)
  | generator (id s t : ℕ)
  | mul (a b : Expression)
  deriving DecidableEq

private def expressionDegree : Expression → ℕ × ℕ
  | .one => (0,0)
  | .named a => a.degree
  | .generator _ s t => (s,t)
  | .mul a b => ((expressionDegree a).1 + (expressionDegree b).1,
      (expressionDegree a).2 + (expressionDegree b).2)

public structure BasisValue where
  expression : Expression
  index : ℕ
  deriving DecidableEq

end
end KIP126.Computation.Table
