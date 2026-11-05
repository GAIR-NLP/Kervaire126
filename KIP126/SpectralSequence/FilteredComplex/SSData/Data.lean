module

import all KIP126.SpectralSequence.FilteredComplex.Data
public import KIP126.SpectralSequence.Basic.Data
import all KIP126.SpectralSequence.Basic.Data
import all KIP126.SpectralSequence.Convergence.Data

@[expose] section

/-!
# Filtered-complex spectral-sequence data

The page operations use the existing filtered-complex structure, its underlying complex and filtration.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- The underlying graded object. -/
@[reducible] def A (FC : FilteredComplex C) : ℤ → C :=
  FC.complex.X

/-- One-index presentation of the chain differential. -/
noncomputable def d (FC : FilteredComplex C) (k : ℤ) :
    FC.A k ⟶ FC.A (k - 1) :=
  FC.complex.d k (k - 1)

/-- The filtration subobjects. -/
@[reducible] def fil (FC : FilteredComplex C) (s k : ℤ) : Subobject (FC.A k) :=
  FC.filtration.F s k

/-- The chosen restriction of the differential to one filtration level. -/
noncomputable def filDiff (FC : FilteredComplex C) (s k : ℤ) :
    Subobject.underlying.obj (FC.fil s k) ⟶
      Subobject.underlying.obj (FC.fil s (k - 1)) :=
  (FC.differential_preserves s k).choose

/-- An associated-graded piece. -/
@[reducible] noncomputable def assocGraded (FC : FilteredComplex C) (s k : ℤ) : C :=
  FC.filtration.associatedGraded s k

/-- The quotient map onto an associated-graded piece. -/
@[reducible] noncomputable def filToAssocGraded (FC : FilteredComplex C) (s k : ℤ) :
    Subobject.underlying.obj (FC.fil s k) ⟶ FC.assocGraded s k :=
  FC.filtration.toAssociatedGraded s k

/-- The differential induced on the associated graded. -/
@[reducible] noncomputable def assocGradedDiff (FC : FilteredComplex C) (s k : ℤ) :
    FC.assocGraded s k ⟶ FC.assocGraded s (k - 1) :=
  FC.associatedGradedDifferential s k

end FilteredComplex

end KIP126.Core.SpectralSequence
