module

import KIP126.Literature
import KIP126.AdamsSynthetic.Completed.Filtration
import Mathlib.GroupTheory.QuotientGroup.Finite
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions

/-! Admissible spectra and a matrix map built from the completed sphere
and its Moore(4) cofiber, for the crossing counterexample construction.
-/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Classical.Adams
open KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum background)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private abbrev S : Spectrum := SphereSpectrum
private abbrev four : S ⟶ S := (4 : ℕ) • 𝟙 S
private abbrev mooreFour : Spectrum := HasFunctorialCofiber.cofib four
private abbrev bottom : S ⟶ mooreFour := HasFunctorialCofiber.cofibι four
private theorem desuspend_injective (X : Spectrum) (n : ℤ) :
    Function.Injective (AbstractAdamsTower.desuspend X n) := by
  let e := (shiftFunctorAdd' Spectrum n (-1) (n-1) (by omega)).app S
  let d := (shiftFunctorCompIsoId Spectrum 1 (-1) (by omega)).app X
  intro a b h
  change e.hom ≫ (shiftFunctor Spectrum (-1 : ℤ)).map a ≫ d.hom =
    e.hom ≫ (shiftFunctor Spectrum (-1 : ℤ)).map b ≫ d.hom at h
  apply (shiftFunctor Spectrum (-1 : ℤ)).map_injective
  apply (cancel_epi e.hom).mp
  apply (cancel_mono d.hom).mp
  simpa only [Category.assoc] using h

private theorem cofiber_connective {X Y : Spectrum} (f : X ⟶ Y)
    (hX : IsConnective X) (hY : IsConnective Y) :
    IsConnective (HasFunctorialCofiber.cofib f) := by
  intro n hn
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang Spectrum := HasFunctorialCofiber.cofib_distinguished f
  have hzero (a : HomotopyGroup n T.obj₃) : a = 0 := by
    haveI := hX (n-1) (by omega)
    have hd : a ≫ T.mor₃ = 0 := desuspend_injective X n (Subsingleton.elim _ _)
    obtain ⟨b, hb⟩ := T.coyoneda_exact₃ hT a hd
    letI : Subsingleton (HomotopyGroup n T.obj₂) := hY n hn
    rw [Subsingleton.elim b 0, zero_comp] at hb
    exact hb
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

private theorem cofiber_finiteModTwoType {X Y : Spectrum} (f : X ⟶ Y)
    (hX : IsFiniteModTwoType background.coefficients X)
    (hY : IsFiniteModTwoType background.coefficients Y) :
    IsFiniteModTwoType background.coefficients (HasFunctorialCofiber.cofib f) := by
  intro n
  let T : HoCofiberSequence (C := Spectrum) :=
    ⟨X, Y, _, f, HasFunctorialCofiber.cofibι f, HasFunctorialCofiber.cofibδ f,
      HasFunctorialCofiber.cofib_distinguished f⟩
  let g := modTwoHomologyMap background.coefficients T.g n
  let δ := modTwoConnecting background.coefficients
    KIP126.AdamsSynthetic.Completed.homologyShift T n
  haveI := hX (n-1)
  haveI := hY n
  letI := Fintype.ofFinite (ModTwoHomology background.coefficients (n-1) X)
  letI := Fintype.ofFinite (ModTwoHomology background.coefficients n Y)
  letI := AddGroup.fintypeOfKerLeRange g δ (fun a ha =>
    (KIP126.AdamsSynthetic.Completed.homology_exact T n a).mp ha)
  infer_instance

private theorem mooreFour_isPaperSpectrum :
    KIP126.AdamsSynthetic.Completed.IsPaperSpectrum mooreFour :=
  ⟨cofiber_connective four KIP126.AdamsSynthetic.Completed.sphere_isPaperSpectrum.1
      KIP126.AdamsSynthetic.Completed.sphere_isPaperSpectrum.1,
    cofiber_finiteModTwoType four KIP126.AdamsSynthetic.Completed.sphere_isPaperSpectrum.2
      KIP126.AdamsSynthetic.Completed.sphere_isPaperSpectrum.2⟩

private theorem mooreFour_isFiniteSpectrum : IsFiniteSpectrum mooreFour :=
  .cofiber (HasFunctorialCofiber.cofib_distinguished four) .sphere .sphere

private def homBiprodEquiv (A X Y : Spectrum) :
    (A ⟶ X ⊞ Y) ≃+ ((A ⟶ X) × (A ⟶ Y)) where
  toFun a := (a ≫ biprod.fst, a ≫ biprod.snd)
  invFun a := biprod.lift a.1 a.2
  left_inv a := by apply biprod.hom_ext <;> simp
  right_inv a := by simp
  map_add' a b := by simp [Preadditive.add_comp]

private theorem biprod_connective {X Y : Spectrum}
    (hX : IsConnective X) (hY : IsConnective Y) : IsConnective (X ⊞ Y) := by
  intro n hn
  letI := hX n hn
  letI := hY n hn
  exact (homBiprodEquiv (Sphere n) X Y).injective.subsingleton

private theorem biprod_finiteModTwoType {X Y : Spectrum}
    (hX : IsFiniteModTwoType background.coefficients X)
    (hY : IsFiniteModTwoType background.coefficients Y) :
    IsFiniteModTwoType background.coefficients (X ⊞ Y) := by
  let H := background.coefficients.object
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.symmetric
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.closed
  let F := tensorLeft H
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  intro n
  haveI := hX n
  haveI := hY n
  let e := (Iso.homCongr (Iso.refl (Sphere n)) (F.mapBiprod X Y)).trans
    (homBiprodEquiv (Sphere n) (H ⊗ X) (H ⊗ Y)).toEquiv
  exact Finite.of_injective e e.injective

private theorem biprod_isPaperSpectrum {X Y : Spectrum}
    (hX : KIP126.AdamsSynthetic.Completed.IsPaperSpectrum X)
    (hY : KIP126.AdamsSynthetic.Completed.IsPaperSpectrum Y) :
    KIP126.AdamsSynthetic.Completed.IsPaperSpectrum (X ⊞ Y) :=
  ⟨biprod_connective hX.1 hY.1, biprod_finiteModTwoType hX.2 hY.2⟩

private def candidateSpectrum : Spectrum := S ⊞ (mooreFour ⊞ S)

private theorem candidate_isPaperSpectrum :
    KIP126.AdamsSynthetic.Completed.IsPaperSpectrum candidateSpectrum :=
  biprod_isPaperSpectrum KIP126.AdamsSynthetic.Completed.sphere_isPaperSpectrum
    (biprod_isPaperSpectrum mooreFour_isPaperSpectrum
      KIP126.AdamsSynthetic.Completed.sphere_isPaperSpectrum)

private def matrixMap : candidateSpectrum ⟶ candidateSpectrum :=
  biprod.lift (biprod.snd ≫ biprod.snd ≫ four)
    (biprod.lift (biprod.fst ≫ bottom) (biprod.fst ≫ ((2 : ℕ) • 𝟙 S)))

private theorem matrixMap_bottom :
    (biprod.inl : S ⟶ candidateSpectrum) ≫ matrixMap ≫ biprod.snd ≫ biprod.fst = bottom := by
  simp [matrixMap]

private theorem factorization_zero_on_homology {X Y : Spectrum} {n : ℕ}
    {f : X ⟶ Y} (h : AdamsMapFactorization background.coefficients n f) :
    ZeroOnModTwoHomology background.coefficients f := by
  cases h with
  | single f hf => exact hf
  | prepend f g hf hg =>
      intro i x
      change x ≫ (background.coefficients.object ◁ (f ≫ g)) = 0
      rw [whiskerLeft_comp, ← Category.assoc]
      change modTwoHomologyMap background.coefficients f i x ≫ _ = 0
      rw [hf i x, zero_comp]

private theorem positive_filtration_zero_on_right_homology {X Y : Spectrum}
    (f : X ⟶ Y) (hf : MapFiltrationAtLeast background.classicalTower f 1)
    (n : ℤ) (a : HomotopyGroup n (X ⊗ background.coefficients.object)) :
    a ≫ (f ▷ background.coefficients.object) = 0 := by
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.symmetric
  have hF : FactorizationFiltration background.coefficients f 1 :=
    (KIP126.AdamsSynthetic.Completed.factorization_filtration_iff f 1).mpr hf
  have hz := factorization_zero_on_homology (hF 1 (by decide) (by decide))
  apply (cancel_mono (β_ Y background.coefficients.object).hom).mp
  rw [Category.assoc, BraidedCategory.braiding_naturality_left, ← Category.assoc]
  change modTwoHomologyMap background.coefficients f n
    (a ≫ (β_ X background.coefficients.object).hom) = _
  rw [hz, zero_comp]

private def coefficientGenerator :
    HomotopyGroup 0 (S ⊗ background.coefficients.object) :=
  background.coefficients.pi0Equiv.symm 1 ≫ (λ_ background.coefficients.object).inv

private theorem coefficientGenerator_ne_zero : coefficientGenerator ≠ 0 := by
  intro hz
  have h := congrArg (fun z => z ≫ (λ_ background.coefficients.object).hom) hz
  have h0 : background.coefficients.pi0Equiv.symm 1 = 0 := by
    simpa only [coefficientGenerator, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      zero_comp] using h
  have h10 : (1 : ZMod 2) = 0 := by
    simpa only [AddEquiv.apply_symm_apply, map_zero] using
      congrArg background.coefficients.pi0Equiv h0
  exact one_ne_zero h10

private theorem bottom_nonzero_on_homology :
    coefficientGenerator ≫ (bottom ▷ background.coefficients.object) ≠ 0 := by
  let H := background.coefficients.object
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.tensorShift H
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.tensorExact H
  let F := tensorRight H
  let T := F.mapTriangle.obj (Triangle.mk four bottom (HasFunctorialCofiber.cofibδ four))
  have hT : T ∈ distTriang Spectrum :=
    F.map_distinguished _ (HasFunctorialCofiber.cofib_distinguished four)
  intro hz
  obtain ⟨b, hb⟩ := T.coyoneda_exact₂ hT coefficientGenerator hz
  change HomotopyGroup 0 (S ⊗ H) at b
  change coefficientGenerator = b ≫ F.map four at hb
  apply coefficientGenerator_ne_zero
  refine hb.trans ?_
  change b ≫ F.map ((4 : ℕ) • 𝟙 S) = 0
  erw [CategoryTheory.Functor.map_nsmul, F.map_id S,
    Preadditive.comp_nsmul, Category.comp_id]
  apply (cancel_mono (λ_ H).hom).mp
  rw [Preadditive.nsmul_comp, zero_comp]
  apply background.coefficients.pi0Equiv.injective
  rw [map_nsmul, map_zero]
  exact (show ∀ z : ZMod 2, (4 : ℕ) • z = 0 by decide) _

private theorem matrixMap_normalizedExponent :
    normalizedExponent background.classicalTower matrixMap = 0 := by
  classical
  apply if_neg
  intro hf
  let H := background.coefficients.object
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.tensorShift H
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.tensorExact H
  let F := tensorRight H
  let a : HomotopyGroup 0 (candidateSpectrum ⊗ H) :=
    coefficientGenerator ≫ F.map (biprod.inl : S ⟶ candidateSpectrum)
  have hz := positive_filtration_zero_on_right_homology matrixMap hf 0 a
  change a ≫ F.map matrixMap = 0 at hz
  apply bottom_nonzero_on_homology
  have h := congrArg (fun z => z ≫ F.map (biprod.snd ≫ biprod.fst)) hz
  have hm : (biprod.inl : S ⟶ candidateSpectrum) ≫ matrixMap ≫
      (biprod.snd ≫ biprod.fst) = bottom := matrixMap_bottom
  change coefficientGenerator ≫ F.map bottom = 0
  rw [← hm, F.map_comp, F.map_comp]
  simpa only [a, Category.assoc, zero_comp] using h

private theorem coefficient_nsmul_four (n : ℤ)
    (a : HomotopyGroup n background.coefficients.object) : (4 : ℕ) • a = 0 := by
  by_cases hn : n = 0
  · subst n
    apply background.coefficients.pi0Equiv.injective
    rw [map_nsmul, map_zero]
    exact (show ∀ z : ZMod 2, (4 : ℕ) • z = 0 by decide) _
  · letI := background.coefficients.homotopy_vanishes n hn
    exact Subsingleton.elim _ _

private theorem four_zero_on_homology :
    ZeroOnModTwoHomology background.coefficients four := by
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.closed
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tensorLeft background.coefficients.object)
  letI := Functor.additive_of_preservesBinaryBiproducts
    (tensorLeft background.coefficients.object)
  intro n a
  let H := background.coefficients.object
  change a ≫ (tensorLeft H).map ((4 : ℕ) • 𝟙 S) = 0
  erw [CategoryTheory.Functor.map_nsmul, (tensorLeft H).map_id S,
    Preadditive.comp_nsmul, Category.comp_id]
  apply (cancel_mono (ρ_ H).hom).mp
  rw [Preadditive.nsmul_comp, zero_comp]
  exact coefficient_nsmul_four n _

private theorem four_filtration_one :
    MapFiltrationAtLeast background.classicalTower four 1 := by
  apply (KIP126.AdamsSynthetic.Completed.factorization_filtration_iff four 1).mp
  intro n hn hn1
  have he : n = 1 := by omega
  subst n
  exact .single four four_zero_on_homology

private theorem four_exponent : normalizedExponent background.classicalTower four = 1 := by
  classical
  exact if_pos four_filtration_one

private theorem bottom_exponent : normalizedExponent background.classicalTower bottom = 0 := by
  classical
  apply if_neg
  intro h
  exact bottom_nonzero_on_homology
    (positive_filtration_zero_on_right_homology bottom h 0 coefficientGenerator)

private theorem top_exponent :
    normalizedExponent background.classicalTower (HasFunctorialCofiber.cofibδ four) = 0 := by
  classical
  apply if_neg
  intro hh
  let H := background.coefficients.object
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.tensorShift H
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.tensorExact H
  let F := tensorRight H
  let T := F.mapTriangle.obj (Triangle.mk four bottom (HasFunctorialCofiber.cofibδ four))
  have hT : T ∈ distTriang Spectrum :=
    F.map_distinguished _ (HasFunctorialCofiber.cofib_distinguished four)
  let a : HomotopyGroup 1 (T.obj₁⟦(1 : ℤ)⟧) :=
    (shiftFunctorAdd' Spectrum 0 1 1 (by omega)).hom.app S ≫
      (shiftFunctor Spectrum (1 : ℤ)).map coefficientGenerator
  have ha : a ≠ 0 := by
    intro hz
    have h : (shiftFunctor Spectrum (1 : ℤ)).map coefficientGenerator = 0 := by
      apply (cancel_epi ((shiftFunctorAdd' Spectrum 0 1 1 (by omega)).hom.app S)).mp
      simpa only [a, comp_zero] using hz
    apply coefficientGenerator_ne_zero
    apply (shiftFunctor Spectrum (1 : ℤ)).map_injective
    simpa only [Functor.map_zero] using h
  have hf : coefficientGenerator ≫ T.mor₁ = 0 :=
    positive_filtration_zero_on_right_homology four four_filtration_one 0 coefficientGenerator
  have haf : a ≫ (shiftFunctor Spectrum (1 : ℤ)).map T.mor₁ = 0 := by
    dsimp only [a]
    rw [Category.assoc, ← Functor.map_comp, hf, Functor.map_zero, comp_zero]
  obtain ⟨b, hb⟩ := T.coyoneda_exact₁ hT a haf
  have hbh : b ≫ T.mor₃ = 0 := by
    change b ≫ ((HasFunctorialCofiber.cofibδ four ▷ H) ≫ _) = 0
    rw [← Category.assoc]
    rw [positive_filtration_zero_on_right_homology _ hh 1 b, zero_comp]
  exact ha (hb.trans hbh)

private def mooreAdamsObject : AdamsObject (coefficients := background.coefficients) :=
  .spectrum mooreFour mooreFour_isPaperSpectrum.isBoundedBelowFiniteModTwoType

private def mooreTriangle : TriangleData background.auxiliary where
  X := .sphere
  Y := .sphere
  Z := mooreAdamsObject
  f := four
  g := bottom
  h := HasFunctorialCofiber.cofibδ four
  distinguished := HasFunctorialCofiber.cofib_distinguished four

private theorem moore_exponent_sum :
    (normalizedExponent background.classicalTower mooreTriangle.f : ℤ) +
      normalizedExponent background.classicalTower mooreTriangle.g +
      normalizedExponent background.classicalTower mooreTriangle.h = 1 := by
  change (normalizedExponent background.classicalTower four : ℤ) +
    normalizedExponent background.classicalTower bottom +
    normalizedExponent background.classicalTower (HasFunctorialCofiber.cofibδ four) = 1
  rw [four_exponent, bottom_exponent, top_exponent]
  norm_num

private theorem moore_normalized_distinguished :
    KIP126.Literature.normalizedTriangle background mooreTriangle moore_exponent_sum ∈
      distTriang KIP126.AdamsSynthetic.Completed.SyntheticSpectrum :=
  KIP126.Literature.Standard.normalized_triangle_distinguished mooreTriangle moore_exponent_sum

private def candidateAdamsObject : AdamsObject (coefficients := background.coefficients) :=
  .spectrum candidateSpectrum candidate_isPaperSpectrum.isBoundedBelowFiniteModTwoType


private def candidateFiniteWindow (q : ℕ) (hq : 0 < q) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < q) :
    ((background.family.quotient (background.nu.functor.obj candidateSpectrum) q).sequence.ssData
      (s,t,w)).eInfty ≃+
      KIP126.Literature.CycleQuotient background candidateAdamsObject
        (q-t+w) (1+t-w) (s,t) :=
  KIP126.Literature.Standard.infinityFiniteWindow candidateAdamsObject q hq (s,t) w hw

private abbrev quotientNu (q : ℕ) : Spectrum ⥤ KIP126.AdamsSynthetic.Completed.SyntheticSpectrum :=
  background.nu.functor ⋙ background.quotients.functoriality.functor q

-- The matrix entries remain the same actual maps after applying ν and Q_q.

private theorem quotientNu_additive (q : ℕ) (hq : 0 < q) : (quotientNu q).Additive := by
  let C := KIP126.Literature.Standard.finiteQuotientComparison q hq
  letI := C.commShift
  letI := C.isTriangulated
  letI := background.nu.additive
  change (background.nu.functor ⋙ background.quotients.functoriality.functor q).Additive
  infer_instance

private def candidateQuotientBiprodIso (q : ℕ) (hq : 0 < q) :
    (quotientNu q).obj candidateSpectrum ≅
      (quotientNu q).obj S ⊞ ((quotientNu q).obj mooreFour ⊞ (quotientNu q).obj S) := by
  let F := quotientNu q
  letI : F.Additive := quotientNu_additive q hq
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := S) (Y := mooreFour ⊞ S)
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := mooreFour) (Y := S)
  exact F.mapBiprod S (mooreFour ⊞ S) ≪≫
    biprod.mapIso (Iso.refl _) (F.mapBiprod mooreFour S)

private theorem candidateQuotient_matrix (q : ℕ) (hq : 0 < q) :
    (candidateQuotientBiprodIso q hq).inv ≫ (quotientNu q).map matrixMap ≫
        (candidateQuotientBiprodIso q hq).hom =
      biprod.lift (biprod.snd ≫ biprod.snd ≫ ((4 : ℕ) • 𝟙 ((quotientNu q).obj S)))
        (biprod.lift (biprod.fst ≫ (quotientNu q).map bottom)
          (biprod.fst ≫ ((2 : ℕ) • 𝟙 ((quotientNu q).obj S)))) := by
  let F := quotientNu q
  let C := KIP126.Literature.Standard.finiteQuotientComparison q hq
  letI := C.commShift
  letI := C.isTriangulated
  letI := background.nu.additive
  letI : F.Additive := quotientNu_additive q hq
  apply (cancel_epi (candidateQuotientBiprodIso q hq).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply biprod.hom_ext
  · simp [candidateQuotientBiprodIso, Category.assoc,
      ← CategoryTheory.Functor.map_comp, matrixMap, four]
  · apply biprod.hom_ext <;>
      simp [candidateQuotientBiprodIso, Category.assoc,
        ← CategoryTheory.Functor.map_comp, matrixMap, four]

open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
open KIP126.Literature
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (SyntheticSpectrum)

private def selectedFourNormalized :
    (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj S) ⟶
      background.nu.functor.obj S :=
  eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k : ℤ))).obj
    (background.nu.functor.obj S)) four_exponent.symm) ≫
      (background.normalizedMap .sphere .sphere four).map

private theorem selectedFourNormalized_factorization :
    lambdaToPositivePow 1 (background.nu.functor.obj S) ≫ selectedFourNormalized =
      background.nu.functor.map four := by
  have transport (e : ℕ) (he : e = 1)
      (F : (SyntheticCategory.biShift (0,(e : ℤ))).obj (background.nu.functor.obj S) ⟶
        background.nu.functor.obj S)
      (hF : lambdaToPositivePow e _ ≫ F = background.nu.functor.map four) :
      lambdaToPositivePow 1 _ ≫
        (eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k : ℤ))).obj
          (background.nu.functor.obj S)) he.symm) ≫ F) = background.nu.functor.map four := by
    subst e
    simpa only [eqToHom_refl, Category.id_comp] using hF
  exact transport _ four_exponent _ (background.normalizedMap .sphere .sphere four).factorization

/-- The factorization determines the chosen normalization. -/
private theorem selectedFourNormalized_eq_two_h0 :
    selectedFourNormalized = (2 : ℕ) • h0NormalizedMap := by
  apply positiveLambda_one_unique
  rw [selectedFourNormalized_factorization, Preadditive.comp_nsmul,
    h0NormalizedMap_factorization]
  letI := background.nu.additive
  rw [← CategoryTheory.Functor.map_nsmul]
  congr 1
  change (4 : ℕ) • 𝟙 S = 2 • (2 • 𝟙 S)
  rw [smul_smul]
  rfl

private def mooreNormalizedTargetIso :
    (normalizedTriangle background mooreTriangle moore_exponent_sum).obj₃ ≅
      background.nu.functor.obj mooreFour :=
  zero_negative_iso _ (normalizedExponent background.classicalTower bottom) bottom_exponent

private theorem moore_normalized_bottom :
    (normalizedTriangle background mooreTriangle moore_exponent_sum).mor₂ ≫
      mooreNormalizedTargetIso.hom = background.nu.functor.map bottom :=
  negative_lift_zero_map_form _ bottom_exponent _ _
    (background.normalizedMap .sphere mooreAdamsObject bottom).factorization

private def mooreNormalizedSourceIso :
    (normalizedTriangle background mooreTriangle moore_exponent_sum).obj₁ ≅
      (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj S) :=
  eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k : ℤ))).obj
    (background.nu.functor.obj S)) four_exponent)

private theorem moore_normalized_four :
    mooreNormalizedSourceIso.inv ≫
      (normalizedTriangle background mooreTriangle moore_exponent_sum).mor₁ =
        (2 : ℕ) • h0NormalizedMap := selectedFourNormalized_eq_two_h0

/-- The actual finite Moore row, with the sphere normalization computed above. -/
private def mooreQuotientTriangle (q : ℕ) (hq : 0 < q) : Triangle SyntheticSpectrum := by
  let C := KIP126.Literature.Standard.finiteQuotientComparison q hq
  letI := C.commShift
  exact (background.quotients.functoriality.functor q).mapTriangle.obj
    (normalizedTriangle background mooreTriangle moore_exponent_sum)

private theorem mooreQuotientTriangle_distinguished (q : ℕ) (hq : 0 < q) :
    mooreQuotientTriangle q hq ∈ distTriang SyntheticSpectrum := by
  let C := KIP126.Literature.Standard.finiteQuotientComparison q hq
  letI := C.commShift
  letI := C.isTriangulated
  exact (background.quotients.functoriality.functor q).map_distinguished _
    moore_normalized_distinguished

private theorem low_sphere_e2_negative_stem (s : ℕ) (hs : 1 ≤ s) (hs' : s ≤ 6) :
    Subsingleton (background.classical.sphere.Page 2 ((s : ℤ), (s : ℤ)-1)) := by
  have he : (s : ℤ)-1 = ((s-1 : ℕ) : ℤ) := by omega
  rw [he]
  have hz : KIP126.Computation.Standard.archive.basisCount s (s-1) = 0 := by
    interval_cases s <;> rfl
  haveI : Subsingleton (Fin (KIP126.Computation.Standard.archive.basisCount s (s-1)) →₀ ZMod 2) := by
    rw [hz]
    infer_instance
  exact (KIP126.Computation.Standard.coordinates s (s-1) (by omega)).injective.subsingleton

/-- Vanishing in the finite negative-stem range of the construction. -/
private theorem finite_sphere_negative_stem (q : ℕ) (hq : 0 < q) (w : ℤ)
    (hw : 0 ≤ w) (hqw : w + q ≤ 6)
    (a : BiHom (-1) w (XModLambdaN (background.nu.functor.obj S) q)) : a = 0 := by
  have hstart : FiltrationAtLeast background.syntheticTower (w+1) a := by
    have H (s m : ℤ) (hm : w-s = m)
        (b : BiHom m w (XModLambdaN (background.nu.functor.obj S) q)) :
        FiltrationAtLeast background.syntheticTower s b := by
      subst m
      exact finite_bottom_filtration .sphere q hq s w b
    exact H (w+1) (-1) (by omega) a
  have hz (j : ℤ) (hj : w+1 ≤ j) (hjt : j < w+1+q) :
      IsZero (((background.family.obj (XModLambdaN (background.nu.functor.obj S) q)).sequence.ssData
        (j,-1+j,w)).eInfty) := by
    haveI : Subsingleton ((background.classical.obj
        (AdamsObject.sphere.obj background.auxiliary)).Page 2 (j,-1+j)) := by
      change Subsingleton (background.classical.sphere.Page 2 (j,-1+j))
      have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
      have h := low_sphere_e2_negative_stem j.toNat (by omega) (by omega)
      simpa only [he, sub_eq_add_neg, add_comm] using h
    haveI : Subsingleton (CycleQuotient background .sphere (q-(-1+j)+w)
        (1+(-1+j)-w) (j,-1+j)) := inferInstance
    letI : Subsingleton (((background.family.obj
        (XModLambdaN (background.nu.functor.obj S) q)).sequence.ssData (j,-1+j,w)).eInfty) :=
      (KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (j,-1+j) w
        (by omega)).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hend := (filtration_iff_of_infinity_zero
    (background.convergence (.quotient q (.nu .sphere))) (w+1) (w+1+q) (-1) w
    (by omega) hz a).mp hstart
  exact finite_high_filtration_zero .sphere q hq (-1) w (w+1+q) (by omega) a hend

private theorem first_sphere_quotient_two (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj S) 1)) :
    (2 : ℕ) • a = 0 := by
  have H (s t : ℤ) (b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj S) 1)) :
      (2 : ℕ) • b = 0 := by
    let Q := background.quotients.functoriality.functor 1
    let e := Q.mapIso background.nu.unitIso
    apply (cancel_mono e.hom).mp
    rw [Preadditive.nsmul_comp, zero_comp]
    apply (KIP126.Literature.sphereFirstQuotient background s t).injective
    rw [map_nsmul, map_zero]
    letI : Module (ZMod 2) (background.classical.sphere.Page 2 (s,t)) :=
      background.sphereAlgebra.scalar (s,t)
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    simp only [ZMod.natCast_self, zero_smul]
  have h := H (w-m) w
  have he : w-(w-m) = m := by omega
  rw [he] at h
  exact h a

/-- The first arrow in the actual Moore quotient row acts by zero on every represented homotopy group. -/
private theorem moore_first_quotient_four_zero (m w : ℤ)
    (a : BiHom m w (mooreQuotientTriangle 1 (by decide)).obj₁) :
    a ≫ (mooreQuotientTriangle 1 (by decide)).mor₁ = 0 := by
  let Q := background.quotients.functoriality.functor 1
  let C := KIP126.Literature.Standard.finiteQuotientComparison 1 (by decide)
  letI := C.commShift
  letI := C.isTriangulated
  let e := Q.mapIso mooreNormalizedSourceIso
  have hf : e.inv ≫ Q.map (normalizedTriangle background mooreTriangle moore_exponent_sum).mor₁ =
      (2 : ℕ) • Q.map h0NormalizedMap := by
    change Q.map mooreNormalizedSourceIso.inv ≫ Q.map _ = _
    erw [← Q.map_comp, moore_normalized_four, Q.map_nsmul]
  change a ≫ Q.map (normalizedTriangle background mooreTriangle moore_exponent_sum).mor₁ = 0
  calc
    _ = (a ≫ e.hom) ≫ (e.inv ≫ Q.map
        (normalizedTriangle background mooreTriangle moore_exponent_sum).mor₁) := by simp
    _ = (2 : ℕ) • ((a ≫ e.hom) ≫ Q.map h0NormalizedMap) := by
      rw [hf, Preadditive.comp_nsmul]
    _ = 0 := first_sphere_quotient_two m w _

/-- Injectivity of the bottom-cell map. -/
private theorem moore_first_quotient_bottom_injective (m w : ℤ) :
    Function.Injective (fun a : BiHom m w (XModLambdaN (background.nu.functor.obj S) 1) =>
      a ≫ (quotientNu 1).map bottom) := by
  intro a b hab
  change a ≫ (quotientNu 1).map bottom = b ≫ (quotientNu 1).map bottom at hab
  let Q := background.quotients.functoriality.functor 1
  let e := Q.mapIso mooreNormalizedTargetIso
  let T := mooreQuotientTriangle 1 (by decide)
  have hg : T.mor₂ ≫ e.hom = (quotientNu 1).map bottom := by
    change Q.map _ ≫ Q.map _ = Q.map _
    rw [← Q.map_comp, moore_normalized_bottom]
  have hz : (a-b) ≫ T.mor₂ = 0 := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, hg, Preadditive.sub_comp, hab, sub_self, zero_comp]
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂ (mooreQuotientTriangle_distinguished 1 (by decide)) (a-b) hz
  exact sub_eq_zero.mp (hc.trans (moore_first_quotient_four_zero m w c))

private theorem moore_finite_boundary_zero (q : ℕ) (hq : 0 < q) (w : ℤ)
    (hw : 1 ≤ w) (hqw : w+q ≤ 7)
    (a : BiHom 0 w ((mooreQuotientTriangle q hq).obj₁⟦(1 : ℤ)⟧)) : a = 0 := by
  let Q := background.quotients.functoriality.functor q
  let A := XModLambdaN (background.nu.functor.obj S) q
  letI := background.exactness.shiftCommShift (0,1)
  letI := background.exactness.shiftExact (0,1)
  obtain ⟨κ, hκ, hκ'⟩ := quotient_shift_exists background.quotients.coherence (0,1) q
    (background.nu.functor.obj S)
  let e : (mooreQuotientTriangle q hq).obj₁ ≅ (SyntheticCategory.biShift (0,1)).obj A :=
    Q.mapIso mooreNormalizedSourceIso ≪≫ κ
  let e' : (mooreQuotientTriangle q hq).obj₁⟦(1 : ℤ)⟧ ≅
      (SyntheticCategory.biShift (1,1)).obj A :=
    (shiftFunctor SyntheticSpectrum (1 : ℤ)).mapIso e ≪≫
      (SyntheticCategory.biShift_compat 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (0,1) (1,0)).app A
  have hz : ∀ b : BiHom (-1) (w-1) A, b = 0 :=
    finite_sphere_negative_stem q hq (w-1) (by omega) (by omega)
  haveI : Subsingleton (BiHom (-1) (w-1) A) := ⟨fun b c => (hz b).trans (hz c).symm⟩
  have hsub := (susp_invariance (-1) (w-1) 1 1 A).symm.injective.subsingleton
  haveI : Subsingleton (BiHom 0 w ((SyntheticCategory.biShift (1,1)).obj A)) := by
    simpa only [neg_add_cancel, sub_add_cancel] using hsub
  apply (cancel_mono e'.hom).mp
  exact Subsingleton.elim _ _

/-- Surjectivity is derived from the actual distinguished row and the finite sphere calculation. -/
private theorem moore_quotient_bottom_surjective (q : ℕ) (hq : 0 < q) (w : ℤ)
    (hw : 1 ≤ w) (hqw : w+q ≤ 7) :
    Function.Surjective (fun a : BiHom 0 w (XModLambdaN (background.nu.functor.obj S) q) =>
      a ≫ (quotientNu q).map bottom) := by
  intro a
  let Q := background.quotients.functoriality.functor q
  let e := Q.mapIso mooreNormalizedTargetIso
  let T := mooreQuotientTriangle q hq
  have hg : T.mor₂ ≫ e.hom = (quotientNu q).map bottom := by
    change Q.map _ ≫ Q.map _ = Q.map _
    rw [← Q.map_comp, moore_normalized_bottom]
  have hz : (a ≫ e.inv) ≫ T.mor₃ = 0 := moore_finite_boundary_zero q hq w hw hqw _
  obtain ⟨b, hb⟩ := T.coyoneda_exact₃ (mooreQuotientTriangle_distinguished q hq) (a ≫ e.inv) hz
  refine ⟨b, ?_⟩
  change b ≫ (quotientNu q).map bottom = a
  rw [← hg, ← Category.assoc, ← hb]
  simp

private theorem moore_first_quotient_bottom_bijective (w : ℤ) (hw : 1 ≤ w) (hw' : w ≤ 6) :
    Function.Bijective (fun a : BiHom 0 w (XModLambdaN (background.nu.functor.obj S) 1) =>
      a ≫ (quotientNu 1).map bottom) :=
  ⟨moore_first_quotient_bottom_injective 0 w,
    moore_quotient_bottom_surjective 1 (by decide) w hw (by omega)⟩

open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples

private def h0Cube : background.classical.sphere.Page 2 (3,3) :=
  product h0 h0Square

private theorem h0Square_basis :
    (coordinates 2 2 (by decide)).symm (Finsupp.single ⟨0, by decide⟩ 1) = h0Square := by
  rw [coordinates_basis]
  have hw : archive.basisMonomial 2 2 ⟨0, by decide⟩ = .mul h0Word h0Word := by rfl
  rw [hw]
  change comparison 2 2 _
    (sourceData.product 1 1 1 1 (h0Word.value sourceData sourceGenerator)
      (h0Word.value sourceData sourceGenerator)) = h0Square
  rw [h0Word_value, comparison_product 1 1 1 1, comparison_h0]
  rfl

private theorem h0Cube_basis :
    (coordinates 3 3 (by decide)).symm (Finsupp.single ⟨0, by decide⟩ 1) = h0Cube := by
  rw [coordinates_basis]
  have hw : archive.basisMonomial 3 3 ⟨0, by decide⟩ = .mul h0Word (.mul h0Word h0Word) := by rfl
  rw [hw]
  change comparison 3 3 _
    (sourceData.product 1 1 2 2 (h0Word.value sourceData sourceGenerator)
      (sourceData.product 1 1 1 1 (h0Word.value sourceData sourceGenerator)
        (h0Word.value sourceData sourceGenerator))) = h0Cube
  rw [h0Word_value, comparison_product 1 1 2 2, comparison_product 1 1 1 1, comparison_h0]
  rfl

private theorem h0Cube_ne_zero : h0Cube ≠ 0 := by
  rw [← h0Cube_basis]
  intro h
  have h' := congrArg (coordinates 3 3 (by decide)) h
  simp only [LinearEquiv.apply_symm_apply, map_zero] at h'
  have he := congrArg (fun z => z ⟨0, by decide⟩) h'
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at he
  exact one_ne_zero he

private def h0SquareLift : BiHom 0 2 (S_0_0 : SyntheticSpectrum) :=
  sphereProduct KIP126.Literature.Standard.syntheticH0 KIP126.Literature.Standard.syntheticH0

private def h0CubeLift : BiHom 0 3 (S_0_0 : SyntheticSpectrum) :=
  sphereProduct KIP126.Literature.Standard.syntheticH0 h0SquareLift

private theorem h0SquareLift_label :
    KIP126.Literature.sphereFirstQuotient background 2 2 (quotientClass 1 h0SquareLift) = h0Square := by
  have h := KIP126.Literature.Standard.first_quotient_action 1 1 1 1
    KIP126.Literature.Standard.syntheticH0
    (quotientClass 1 KIP126.Literature.Standard.syntheticH0)
  change KIP126.Literature.sphereFirstQuotient background 2 2
      (sphereAction KIP126.Literature.Standard.syntheticH0
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0)) =
    background.sphereAlgebra.product (1,1) (1,1)
      (KIP126.Literature.sphereFirstQuotient background 1 1
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0))
      (KIP126.Literature.sphereFirstQuotient background 1 1
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0)) at h
  erw [KIP126.Literature.Standard.syntheticH0_first_quotient_label] at h
  change _ = background.sphereAlgebra.product (1,1) (1,1) h0 h0
  simpa only [h0SquareLift, quotientClass, sphereAction, sphereProduct, Category.assoc,
    h0Square, product, h0, eqToHom_refl, ModuleCat.id_apply] using h

private theorem h0CubeLift_label :
    KIP126.Literature.sphereFirstQuotient background 3 3 (quotientClass 1 h0CubeLift) = h0Cube := by
  have h := KIP126.Literature.Standard.first_quotient_action 1 1 2 2
    KIP126.Literature.Standard.syntheticH0 (quotientClass 1 h0SquareLift)
  change KIP126.Literature.sphereFirstQuotient background 3 3
      (sphereAction KIP126.Literature.Standard.syntheticH0 (quotientClass 1 h0SquareLift)) =
    background.sphereAlgebra.product (1,1) (2,2)
      (KIP126.Literature.sphereFirstQuotient background 1 1
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0))
      (KIP126.Literature.sphereFirstQuotient background 2 2 (quotientClass 1 h0SquareLift)) at h
  erw [KIP126.Literature.Standard.syntheticH0_first_quotient_label, h0SquareLift_label] at h
  change _ = background.sphereAlgebra.product (1,1) (2,2) h0 h0Square
  simpa only [h0CubeLift, quotientClass, sphereAction, sphereProduct, Category.assoc,
    h0Cube, product, h0, eqToHom_refl, ModuleCat.id_apply] using h

open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Internal.MahowaldLeibniz

private theorem h1_basis :
    (coordinates 1 2 (by decide)).symm (Finsupp.single ⟨0, by decide⟩ 1) = h1 := by
  rw [coordinates_basis]
  have hw : archive.basisMonomial 1 2 ⟨0, by decide⟩ =
      regradeMonomial rfl rfl (.generator (archive.atomIndex .h1)) := by rfl
  rw [hw]
  have hv : (regradeMonomial rfl rfl (.generator (archive.atomIndex .h1))).value
      sourceData sourceGenerator = sourceData.atom .h1 := sourceAtom_agrees .h1
  rw [hv, comparison_h1]

private theorem permanent_reaches {E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {x : E.Page 2 p} (h : IsPermanentCycle E p x)
    (r : ℤ) (hr : 2 ≤ r) : ReachesPage E r p x := by
  obtain ⟨z, hz⟩ := h
  let D := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let z' := Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z
  refine ⟨D.pageπ n z', hr, z', ?_, rfl⟩
  dsimp only [z']
  rw [← ModuleCat.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact hz

private theorem h1_d2_zero : background.classical.sphere.d 2 (1,2) = 0 := by
  ext x
  rcases one_coordinate_label_cases rfl (coordinates 1 2 (by decide)) h1 h1_basis x with h | h
  · simp only [h, map_zero]
  · subst x
    obtain ⟨z, hz, _⟩ := KIP126.Literature.Standard.eta_permanent
    have hp : IsPermanentCycle background.classical.sphere (1,2) h1 := ⟨z, hz⟩
    exact represents_d_zero_of_later
      (by rw [background.classical.firstPage]) (by decide : (2 : ℤ) < 3)
      (RepresentsOnPage.self_two h1) (permanent_reaches hp 3 (by decide))

private theorem h0Cube_no_incoming (r : ℤ) (hr : 2 ≤ r) :
    background.classical.sphere.d r ((3,3)-background.classical.sphere.diffDeg r) = 0 := by
  by_cases h2 : r = 2
  · subst r
    have hd : ((3 : ℤ),3)-background.classical.sphere.diffDeg 2 = (1,2) := by
      rw [background.classical.differentialDegree]; rfl
    rw [hd]
    exact h1_d2_zero
  by_cases h3 : r = 3
  · subst r
    haveI := KIP126.AdamsSynthetic.Completed.sphere_page_filtration_zero 3 1 (by decide)
    have hd : ((3 : ℤ),3)-background.classical.sphere.diffDeg 3 = (0,1) := by
      rw [background.classical.differentialDegree]; rfl
    haveI : Subsingleton (background.classical.sphere.Page 3
        ((3,3)-background.classical.sphere.diffDeg 3)) := by rw [hd]; infer_instance
    ext a
    simp only [Subsingleton.elim a 0, map_zero]
  · let p := ((3 : ℤ),3)-background.classical.sphere.diffDeg r
    have hs : p.1 < 0 := by
      dsimp [p]
      rw [background.classical.differentialDegree]
      change 3-r < 0
      omega
    letI : Subsingleton (background.classical.sphere.Page r p) :=
      KIP126.AdamsSynthetic.Completed.classical_page_negative .sphere r p.1 p.2 hs
    ext a
    simp only [Subsingleton.elim a 0, map_zero]

private theorem h0Cube_boundaries_eq_bot (b : ℤ) :
    boundaries background .sphere b (3,3) = ⊥ := by
  let E := background.classical.obj (AdamsObject.sphere.obj background.auxiliary)
  let D := E.ssData (3,3)
  have htop : D.B ⊤ = D.B 0 := by
    have h := boundaries_top_eq_of_d_eq_zero E 2
      (by rw [background.classical.firstPage]) (3,3) h0Cube_no_incoming
    simpa only [D, E, background.classical.firstPage, sub_self, Int.toNat_zero,
      Nat.cast_zero] using h
  have hB : D.B (↑(b-1).toNat) = D.B 0 :=
    le_antisymm ((D.B_mono le_top).trans htop.le) (D.B_mono bot_le)
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    let i := Subobject.ofLE (D.B (↑(b-1).toNat)) (D.B 0) hB.le
    have hi : i ≫ boundaryLabel background .sphere 0 (3,3) =
        boundaryLabel background .sphere (↑(b-1).toNat) (3,3) := by
      dsimp only [i, boundaryLabel, D, E]
      rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    have hz : boundaryLabel background .sphere 0 (3,3) (i z) ∈
        boundaries background .sphere 1 (3,3) := ⟨i z, rfl⟩
    rw [boundaries_one] at hz
    change boundaryLabel background .sphere (↑(b-1).toNat) (3,3) z = 0
    rw [← hi, ModuleCat.comp_apply]
    exact hz
  · exact bot_le

private def h0CubeNu : BiHom 0 3 (background.nu.functor.obj S) :=
  h0CubeLift ≫ background.nu.unitIso.inv

private theorem h0CubeNu_label :
    h0CubeNu ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 3 3 h0Cube := by
  let Q := background.quotients.functoriality.functor 1
  apply (cancel_mono (Q.mapIso background.nu.unitIso).hom).mp
  apply (KIP126.Literature.sphereFirstQuotient background 3 3).injective
  change KIP126.Literature.sphereFirstQuotient background 3 3
      ((h0CubeNu ≫ XModLambdaN.incl _ 1) ≫ XModLambdaN.map background.nu.unitIso.hom 1) =
    KIP126.Literature.sphereFirstQuotient background 3 3
      (nativeFirstLabel .sphere 3 3 h0Cube ≫ XModLambdaN.map background.nu.unitIso.hom 1)
  rw [sphere_native_quotient_label]
  have he : (h0CubeNu ≫ XModLambdaN.incl _ 1) ≫ Q.map background.nu.unitIso.hom =
      quotientClass 1 h0CubeLift := by
    change ((h0CubeLift ≫ background.nu.unitIso.inv) ≫ XModLambdaN.incl _ 1) ≫
        XModLambdaN.map background.nu.unitIso.hom 1 = h0CubeLift ≫ XModLambdaN.incl _ 1
    rw [Category.assoc, ← XModLambdaN.incl_naturality background.nu.unitIso.hom 1]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  exact he ▸ h0CubeLift_label

private theorem h0Cube_permanent : h0Cube ∈ permanentCycles background .sphere (3,3) :=
  first_label_lift_permanent .sphere 3 3 h0Cube h0CubeNu h0CubeNu_label

end
end KIP126.ProofTools.Internal.CrossingCounterexample
