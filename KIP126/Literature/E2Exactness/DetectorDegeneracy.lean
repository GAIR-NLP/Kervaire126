module

import all KIP126.Literature.Standard.FiniteQuotientObjectCases
import KIP126.AdamsSynthetic.Completed.Acyclic

/-! Acyclicity of all-detector homology-short-exact triangles from the
ordinary-source Adams tower theorem. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

private theorem selected_e2_subsingleton_of_homology_zero
    (X : ClassicalObject)
    (hH : ∀ n : ℤ, Subsingleton
      (ModTwoHomology background.coefficients n (X.obj background.auxiliary)))
    (s t : ℤ) :
    Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) := by
  exact classical_page_subsingleton_of_homology_zero
    (X.obj background.auxiliary) hH 2 s t

private theorem detector_homology_subsingleton_of_short_exact
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h))
    (a b c : ℤ)
    (hX : object_cases_detector_shift_weight T.X = some a)
    (hY : object_cases_detector_shift_weight T.Y = some b)
    (hZ : object_cases_detector_shift_weight T.Z = some c) :
    ∀ n : ℤ, Subsingleton (ModTwoHomology background.coefficients n tmf) := by
  intro n
  apply not_nontrivial_iff_subsingleton.mp
  intro hn
  exact object_cases_no_short_exact_three_tmf_shifts
    (Triangle.mk T.f T.g T.h) hH a b c
    (object_cases_detectorShiftHomologyAddEquiv T.X a · hX)
    (object_cases_detectorShiftHomologyAddEquiv T.Y b · hY)
    (object_cases_detectorShiftHomologyAddEquiv T.Z c · hZ) ⟨n, hn⟩

private theorem detector_shift_homology_subsingleton
    (X : ClassicalObject) (a : ℤ)
    (hX : object_cases_detector_shift_weight X = some a)
    (hH : ∀ n : ℤ, Subsingleton (ModTwoHomology background.coefficients n tmf)) :
    ∀ n : ℤ, Subsingleton
      (ModTwoHomology background.coefficients n (X.obj background.auxiliary)) := by
  intro n
  letI := hH (n-a)
  exact ⟨fun u v => (object_cases_detectorShiftHomologyAddEquiv X a n hX).injective
    (Subsingleton.elim _ _)⟩

/-- A homology-short-exact triangle whose three vertices are detector
shifts has zero E₂ groups. -/
private theorem all_detector_e2_subsingleton_of_short_exact
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h))
    (a b c : ℤ)
    (hX : object_cases_detector_shift_weight T.X = some a)
    (hY : object_cases_detector_shift_weight T.Y = some b)
    (hZ : object_cases_detector_shift_weight T.Z = some c) :
    (∀ s t : ℤ, Subsingleton
      ((background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t))) ∧
    (∀ s t : ℤ, Subsingleton
      ((background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s,t))) ∧
    (∀ s t : ℤ, Subsingleton
      ((background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s,t))) := by
  have hz := detector_homology_subsingleton_of_short_exact T hH a b c hX hY hZ
  exact ⟨selected_e2_subsingleton_of_homology_zero T.X
      (detector_shift_homology_subsingleton T.X a hX hz),
    selected_e2_subsingleton_of_homology_zero T.Y
      (detector_shift_homology_subsingleton T.Y b hY hz),
    selected_e2_subsingleton_of_homology_zero T.Z
      (detector_shift_homology_subsingleton T.Z c hZ hz)⟩

end
end KIP126.Literature.Standard
