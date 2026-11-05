module

public import KIP126.AdamsSynthetic.Completed.Coefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! Steenrod Ext from actual stable mod-two cohomology operations.

The operation category has the integer suspensions of the fixed HF₂ object
as objects and actual stable maps as morphisms. Its additive modules include
the represented cohomology of every completed spectrum. Internal degree `t`
is fixed by the cohomology of the actual suspended sphere `Σᵗ1`.
-/

@[expose] section
namespace KIP126.Literature.SteenrodExt
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization
open KIP126.AdamsSynthetic
noncomputable section

/-- The fixed coefficient spectrum in cohomological degree `n`. -/
public def operationObject (n : ℤ) : Completed.Spectrum :=
  (shiftFunctor Completed.Spectrum n).obj Completed.coefficients.object

/-- Stable mod-two operations from degree `n` to degree `m` are actual maps
`ΣⁿHF₂ ⟶ ΣᵐHF₂`; their composition and addition are inherited from spectra. -/
public abbrev Operations :=
  InducedCategory Completed.Spectrum operationObject

/-- Internally graded modules over the stable mod-two operations, with
degree-preserving natural transformations. Additivity is part of each object. -/
public abbrev Modules :=
  Operations ⥤+ AddCommGrpCat.{0}

/-- Additive operation modules are closed under the pointwise abelian
constructions in the ambient functor category. -/
public theorem additiveModulesClosed :
    (additiveFunctor Operations AddCommGrpCat.{0}).ContainsZero ∧
    (additiveFunctor Operations AddCommGrpCat.{0}).IsClosedUnderKernels ∧
    (additiveFunctor Operations AddCommGrpCat.{0}).IsClosedUnderCokernels ∧
    (additiveFunctor Operations AddCommGrpCat.{0}).IsClosedUnderFiniteProducts := by
  sorry

/-- The abelian structure uses the existing pointwise addition on natural
transformations and the full subcategory of additive functors. -/
public instance modulesAbelian : Abelian Modules := by
  letI := additiveModulesClosed.1
  letI := additiveModulesClosed.2.1
  letI := additiveModulesClosed.2.2.1
  letI := additiveModulesClosed.2.2.2
  exact inferInstance

/-- Actual mod-two cohomology: at degree `n` this is `[X, ΣⁿHF₂]`,
and a stable operation acts by postcomposition. -/
public def cohomology (X : Completed.Spectrum) : Modules :=
  AdditiveFunctor.of
    (inducedFunctor operationObject ⋙
      preadditiveCoyoneda.obj (Opposite.op X))

/-- The coefficient module in internal degree `t` is the actual cohomology
of `Σᵗ1`; its value in degree `n` is `[Σᵗ1, ΣⁿHF₂]`. -/
public def coefficientModule (t : ℤ) : Modules :=
  cohomology ((shiftFunctor Completed.Spectrum t).obj (𝟙_ Completed.Spectrum))

public local instance : HasExt.{1} Modules := HasExt.standard Modules

/-- Derived Steenrod Ext with cohomological degree `s` and internal degree
`t`. This is derived Ext in the additive operation-module category, with
the represented cohomology of `X` as source and that of `Σᵗ1` as target. -/
public def ext (X : Completed.Spectrum) (s t : ℤ) : Type 1 :=
  SmallShiftedHom
    (HomologicalComplex.quasiIso Modules (ComplexShape.up ℤ))
    ((CochainComplex.singleFunctor Modules 0).obj (cohomology X))
    ((CochainComplex.singleFunctor Modules 0).obj (coefficientModule t)) s

public instance extAddCommGroup (X : Completed.Spectrum) (s t : ℤ) :
    AddCommGroup (ext X s t) :=
  letI := HasDerivedCategory.standard Modules
  (SmallShiftedHom.equiv
    (HomologicalComplex.quasiIso Modules (ComplexShape.up ℤ))
    DerivedCategory.Q).addCommGroup

public instance extIntModule (X : Completed.Spectrum) (s t : ℤ) :
    Module ℤ (ext X s t) := inferInstance

/-- For nonnegative cohomological degrees this is mathlib's derived Ext. -/
public theorem ext_nat (X : Completed.Spectrum) (s : ℕ) (t : ℤ) :
    ext X (s : ℤ) t =
      CategoryTheory.Abelian.Ext.{1} (cohomology X) (coefficientModule t) s := rfl

end
end KIP126.Literature.SteenrodExt
