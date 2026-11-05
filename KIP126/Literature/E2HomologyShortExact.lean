module
public import KIP126.Literature.Standard
public import KIP126.Literature.E2Exactness.SpectrumHomologyShortExact
import all KIP126.Literature.E2Exactness.FirstQuotientConnecting
import all KIP126.Literature.E2Exactness.DetectorDegeneracy
import all KIP126.Literature.Standard.FiniteQuotientNormalized

/-! H-short-exact triangles and their first-quotient connecting maps. -/
@[expose] section
namespace KIP126.Literature.Standard.E2Exactness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.Literature.Standard.Internal Internal.GhostBounds
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option Elab.async false

private theorem actual_row_rotate_finite_third
    (X Y Z : ClassicalObject) (hZ : ghost_cells_literal_finite_source_case Z)
    (ef eg : ℕ) {A C : SyntheticSpectrum}
    (aCoord : A ≅ (SyntheticCategory.biShift (0,(ef:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))
    (cCoord : C ≅ (SyntheticCategory.biShift (0,-(eg:ℤ))).obj
      (background.nu.functor.obj (Z.obj background.auxiliary)))
    (f : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary))
    (g : background.nu.functor.obj (Y.obj background.auxiliary) ⟶ C)
    (h : C ⟶ A⟦(1:ℤ)⟧)
    (hN : Triangle.mk f g h ∈ distTriang SyntheticSpectrum)
    (q : ℕ) (hq : 0<q) :
    let N := Triangle.mk f g h
    ∃ eB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q ≫ eB.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫
          eB.hom)) ∈ distTriang SyntheticSpectrum := by
  let N := Triangle.mk f g h
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let bCoord : N.obj₂ ≅ (SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  obtain ⟨eA,heA,hR0⟩ := normalized_mapped_row_finite_third_coordinates
    N hN X Y Z hZ (0,(ef:ℤ)) (0,0) (0,-(eg:ℤ)) 0 aCoord bCoord
    (cCoord ≪≫ (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _)
    (by dsimp only; omega) (by dsimp only; omega) q hq
  let V := Triangle.mk (S.map N.mor₁) (S.map N.mor₂) (-(S.map N.mor₃))
  have hV : V ∈ distTriang SyntheticSpectrum := normalized_raw_suspension_distinguished N hN
  let vaCoord : V.obj₁ ≅ (SyntheticCategory.biShift (1,(ef:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) :=
    S.mapIso aCoord ≪≫ (SyntheticCategory.biShift_compat 1).symm.app _ ≪≫
      (biShiftAddIso (0,(ef:ℤ)) (1,0) (1,(ef:ℤ)) (by ext <;> simp)).app _
  let vbCoord : V.obj₂ ≅ (SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    (SyntheticCategory.biShift_compat 1).symm.app _
  let vcCoord : V.obj₃ ≅ ((SyntheticCategory.biShift (0,-(eg:ℤ))).obj
      (background.nu.functor.obj (Z.obj background.auxiliary)))⟦(1:ℤ)⟧ := S.mapIso cCoord
  obtain ⟨eSA,heSA,hR1⟩ := normalized_mapped_row_finite_third_coordinates
    V hV X Y Z hZ (1,(ef:ℤ)) (1,0) (0,-(eg:ℤ)) 1 vaCoord vbCoord vcCoord
    (by dsimp only; omega) (by dsimp only; omega) q hq
  let Q := background.quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  change Triangle.mk (XModLambdaN.map (S.map N.mor₁) q)
    (XModLambdaN.map (S.map N.mor₂) q)
    (XModLambdaN.map (-(S.map N.mor₃)) q≫eSA.hom) ∈ distTriang SyntheticSpectrum at hR1
  have hneg : XModLambdaN.map (-(S.map N.mor₃)) q=
      -XModLambdaN.map (S.map N.mor₃) q := by
    change Q.map (-_) = -Q.map _
    exact Functor.map_neg Q
  rw [hneg,Preadditive.neg_comp] at hR1
  obtain ⟨eC,heC⟩ := finite_quotient_suspension_comparison q N.obj₃
  obtain ⟨eB,heB,hf⟩ := finite_c_middle_suspension_comparison_of_coordinates
    X Y Z hZ ef eg aCoord cCoord N.mor₁ N.mor₂ N.mor₃ hN q hq
    eA heA eC heC eSA heSA hR0 hR1
  exact ⟨eB,heB,finite_c_public_row_of_middle_comparison N q eA eB hR0 hf⟩



/-- The Qq row of a ν triangle, with first two arrows νf and νg. -/
private theorem selected_nu_quotient_row
    (T : SelectedTriangleData background.auxiliary)
    (δ : background.nu.functor.obj (T.Z.obj background.auxiliary) ⟶
      (background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧)
    (hN : Triangle.mk (background.nu.functor.map T.f) (background.nu.functor.map T.g) δ ∈
      distTriang SyntheticSpectrum)
    (hfinite : ghost_cells_literal_finite_source_case T.X ∨
      ghost_cells_literal_finite_source_case T.Y ∨
      ghost_cells_literal_finite_source_case T.Z)
    (q : ℕ) (hq : 0<q) :
    ∃ ε : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) q ≅
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q ≫ ε.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) q)
        (XModLambdaN.map (background.nu.functor.map T.g) q)
        (XModLambdaN.map δ q ≫ ε.hom) ∈ distTriang SyntheticSpectrum := by
  let N := Triangle.mk (background.nu.functor.map T.f) (background.nu.functor.map T.g) δ
  let ex : N.obj₁ ≅ (SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  let ey : N.obj₂ ≅ (SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (T.Y.obj background.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  let ez : N.obj₃ ≅ (SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (T.Z.obj background.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  rcases hfinite with hX | hY | hZ
  · obtain ⟨X0,n,hX0,⟨ea⟩⟩ := normalized_literal_finite_nu_coordinates T.X hX
    exact actual_finite_first_quotient_row_of_coordinates N hN X0 T.Y T.Z hX0
      (n,n) (0,0) (0,0) ea ey ez q hq (by omega) (by omega)
  · let M := N.invRotate
    let ea : M.obj₁ ≅ (SyntheticCategory.biShift (0,(1:ℤ))).obj
        (background.nu.functor.obj ((ClassicalObject.shift (-1) T.Z).obj background.auxiliary)) :=
      (shiftFunctor SyntheticSpectrum (-1:ℤ)).mapIso ez ≪≫
        normalized_ordinary_shift_coordinate T.Z 0 (-1)
    obtain ⟨ε,hε,hrow⟩ := actual_row_rotate_finite_third
      (.shift (-1) T.Z) T.X T.Y hY 1 0 ea ey
      M.mor₁ M.mor₂ M.mor₃ (inv_rot_of_distTriang N hN) q hq
    exact ⟨ε,hε,normalized_mapped_row_from_inverse_rotation N q ε hrow⟩
  · exact normalized_mapped_row_finite_third_coordinates N hN T.X T.Y T.Z hZ
      (0,0) (0,0) (0,0) 0 ex ey
      (ez ≪≫ (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _)
      (by omega) (by omega) q hq

private def hsesFiniteVertices (T : SelectedTriangleData background.auxiliary) : Prop :=
  ghost_cells_literal_finite_source_case T.X ∨
    ghost_cells_literal_finite_source_case T.Y ∨
    ghost_cells_literal_finite_source_case T.Z

private theorem hses_finite_or_zero
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h)) :
    hsesFiniteVertices T ∨
      ((∀ s t, Subsingleton (Ambient background T.X (s,t))) ∧
       (∀ s t, Subsingleton (Ambient background T.Y (s,t))) ∧
       (∀ s t, Subsingleton (Ambient background T.Z (s,t)))) := by
  rcases hx : object_cases_detector_shift_weight T.X with _ | a
  · exact Or.inl (Or.inl (ghost_cells_descriptor_none_literal_actual T.X hx))
  rcases hy : object_cases_detector_shift_weight T.Y with _ | b
  · exact Or.inl (Or.inr (Or.inl (ghost_cells_descriptor_none_literal_actual T.Y hy)))
  rcases hz : object_cases_detector_shift_weight T.Z with _ | c
  · exact Or.inl (Or.inr (Or.inr (ghost_cells_descriptor_none_literal_actual T.Z hz)))
  exact Or.inr (all_detector_e2_subsingleton_of_short_exact T hH a b c hx hy hz)

/-- Boundary chosen once from the ν preservation theorem for
this same actual H-short-exact classical triangle. -/
private def hsesNuBoundary
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h)) :
    background.nu.functor.obj (T.Z.obj background.auxiliary) ⟶
      (background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧ :=
  Classical.choose (background.nuExactTriangle (Triangle.mk T.f T.g T.h) T.distinguished hH)

private theorem hsesNuBoundary_distinguished
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h)) :
    Triangle.mk (background.nu.functor.map T.f) (background.nu.functor.map T.g)
      (hsesNuBoundary T hH) ∈ distTriang SyntheticSpectrum :=
  Classical.choose_spec (background.nuExactTriangle (Triangle.mk T.f T.g T.h) T.distinguished hH)

/-- Choose the actual inclusion-compatible suspension comparison. In the
finite branch this is the one constructed together with the actual Q₁ row;
in the acyclic branch every selected E₂ group is zero. -/
private def hsesQuotientSuspension
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h)) :
    XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧ := by
  classical
  exact if hfinite : hsesFiniteVertices T then
    Classical.choose (selected_nu_quotient_row T (hsesNuBoundary T hH)
      (hsesNuBoundary_distinguished T hH) hfinite 1 (by omega))
  else Classical.choose (finite_quotient_suspension_comparison 1
    (background.nu.functor.obj (T.X.obj background.auxiliary)))

private theorem hsesQuotientSuspension_inclusion
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h)) :
    XModLambdaN.incl _ 1 ≫ (hsesQuotientSuspension T hH).hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (XModLambdaN.incl (background.nu.functor.obj (T.X.obj background.auxiliary)) 1) := by
  classical
  by_cases hf : hsesFiniteVertices T
  · simpa only [hsesQuotientSuspension,dif_pos hf] using
      (Classical.choose_spec (selected_nu_quotient_row T (hsesNuBoundary T hH)
        (hsesNuBoundary_distinguished T hH) hf 1 (by omega))).1
  · simpa only [hsesQuotientSuspension,dif_neg hf] using
      Classical.choose_spec (finite_quotient_suspension_comparison 1
        (background.nu.functor.obj (T.X.obj background.auxiliary)))

private theorem hsesQuotientSuspension_row
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h))
    (hf : hsesFiniteVertices T) :
    Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) 1)
      (XModLambdaN.map (background.nu.functor.map T.g) 1)
      (XModLambdaN.map (hsesNuBoundary T hH) 1 ≫ (hsesQuotientSuspension T hH).hom) ∈
      distTriang SyntheticSpectrum := by
  classical
  simpa only [hsesQuotientSuspension,dif_pos hf] using
    (Classical.choose_spec (selected_nu_quotient_row T (hsesNuBoundary T hH)
      (hsesNuBoundary_distinguished T hH) hf 1 (by omega))).2

/-- E₂ connecting operation of an H-short-exact classical triangle, of
bidegree (1,0), induced by the ν-triangle boundary and its first-quotient
suspension comparison. -/
@[no_expose] public def selectedE2HomologyShortExactConnectingHom
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h))
    (s t : ℤ) : (background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s,t) →+ (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s+1,t) :=
  by exact hsesConnectingHom T (hsesNuBoundary T hH) (hsesQuotientSuspension T hH) s t

/-- The H-short-exact E₂ long exact sequence on the selected `ClassicalObject`
closure. Its first two maps come from the classical Adams functor,
and its connecting map is the operation constructed above. -/
public theorem selectedE2HomologyShortExactLongExactSequence
    (T : SelectedTriangleData background.auxiliary)
    (hH : HomologyShortExact background.coefficients (Triangle.mk T.f T.g T.h))
    (s t : ℤ) :
    (∀ y : (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s,t),
      (background.classical.map T.g).pageMap 2 (s,t) y=0 ↔
        ∃ x : (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t), (background.classical.map T.f).pageMap 2 (s,t) x=y) ∧
    (∀ z : (background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s,t),
      selectedE2HomologyShortExactConnectingHom T hH s t z=0 ↔
        ∃ y : (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s,t), (background.classical.map T.g).pageMap 2 (s,t) y=z) ∧
    (∀ x : (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s+1,t),
      (background.classical.map T.f).pageMap 2 (s+1,t) x=0 ↔
        ∃ z : (background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s,t), selectedE2HomologyShortExactConnectingHom T hH s t z=x) := by
  rcases hses_finite_or_zero T hH with hf | ⟨hX,hY,hZ⟩
  · have hR := hsesQuotientSuspension_row T hH hf
    exact ⟨hses_exact_at_Y T _ _ hR s t,
      hses_exact_at_Z T _ _ hR s t,hses_exact_at_X T _ _ hR s t⟩
  · refine ⟨?_,?_,?_⟩
    · intro y
      constructor
      · intro _; exact ⟨0,(hY s t).elim _ _⟩
      · intro _; exact (hZ s t).elim _ _
    · intro z
      constructor
      · intro _; exact ⟨0,(hZ s t).elim _ _⟩
      · intro _; exact (hX (s+1) t).elim _ _
    · intro x
      constructor
      · intro _; exact ⟨0,(hX (s+1) t).elim _ _⟩
      · intro _; exact (hY (s+1) t).elim _ _

end
end KIP126.Literature.Standard.E2Exactness
