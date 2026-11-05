module
import all KIP126.Literature.BocksteinLambdaTower
import all KIP126.Literature.BocksteinOriginalSuccessor
import KIP126.AdamsSynthetic.Completed
import KIP126.Literature.SyntheticComparison
import KIP126.SpectralSequence.Computation.State.Proofs

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private def affineWeight (a : ℤ) (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (p.1, p.2.1, p.2.2-a)

private theorem affineWeight_add_degree (a r : ℤ) (p : ℤ × ℤ × ℤ) :
    affineWeight a (p+(r,r-1,0)) = affineWeight a p+(r,r-1,0) := by
  simp [affineWeight]

private def shiftedLambdaDifferential (Y : Syn) (a r : ℤ) (p : ℤ × ℤ × ℤ) :
    ((lambdaSequence Y).ssData (affineWeight a p)).page (↑(r-2).toNat : WithTop ℕ) ⟶
      ((lambdaSequence Y).ssData (affineWeight a (p+(r,r-1,0)))).page
        (↑(r-2).toNat : WithTop ℕ) := by
  simpa only [affineWeight_add_degree, lambdaSequence_first,
    lambdaSequence_degree] using (lambdaSequence Y).d r (affineWeight a p)

private theorem shiftedLambdaDifferential_heq (Y : Syn) (a r : ℤ)
    (p : ℤ × ℤ × ℤ) :
    HEq (shiftedLambdaDifferential Y a r p)
      ((lambdaSequence Y).d r (affineWeight a p)) := by
  unfold shiftedLambdaDifferential
  exact eqMpr_heq' _ _

private def shiftedLambdaPreSequence (Y : Syn) (a : ℤ) :
    PreSS (ModuleCat.{v} ℤ) (ℤ × ℤ × ℤ) where
  r₀ := 2
  ssData p := (lambdaSequence Y).ssData (affineWeight a p)
  diffDeg r := (r,r-1,0)
  d := shiftedLambdaDifferential Y a

private theorem shiftedLambdaDifferential_comp (Y : Syn) (a r : ℤ)
    (p : ℤ × ℤ × ℤ) :
    shiftedLambdaDifferential Y a r p ≫
      shiftedLambdaDifferential Y a r (p+(r,r-1,0)) = 0 := by
  let E := lambdaSequence Y
  have hB : (E.ssData (affineWeight a (p+(r,r-1,0)))).page
      (↑(r-2).toNat : WithTop ℕ) =
      E.Page r (affineWeight a p+E.diffDeg r) := by
    simp only [Page, E, lambdaSequence_first, lambdaSequence_degree,
      affineWeight_add_degree]
  have hC : (E.ssData (affineWeight a ((p+(r,r-1,0))+(r,r-1,0)))).page
      (↑(r-2).toNat : WithTop ℕ) =
      E.Page r ((affineWeight a p+E.diffDeg r)+E.diffDeg r) := by
    simp only [Page, E, lambdaSequence_first, lambdaSequence_degree,
      affineWeight_add_degree]
  have hg : HEq (shiftedLambdaDifferential Y a r (p+(r,r-1,0)))
      (E.d r (affineWeight a p+E.diffDeg r)) := by
    refine (shiftedLambdaDifferential_heq Y a r _).trans ?_
    exact dependent_apply_heq (E.d r) (affineWeight_add_degree a r p)
  exact composition_zero_of_heq rfl hB hC
    (shiftedLambdaDifferential_heq Y a r p) hg (E.d_comp_d r (affineWeight a p))

private def shiftedLambdaSequence (Y : Syn) (a : ℤ) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ × ℤ) where
  toPreSS := shiftedLambdaPreSequence Y a
  d_comp_d := shiftedLambdaDifferential_comp Y a
  Z_succ r p hr := by
    let E := lambdaSequence Y
    refine kernel_eq_of_heq rfl ?_ (shiftedLambdaDifferential_heq Y a r p)
      (HEq.rfl) (E.Z_succ r (affineWeight a p) hr)
    simp only [shiftedLambdaPreSequence, lambdaSequence_first, lambdaSequence_degree,
      affineWeight_add_degree]
  B_succ r p hr := by
    let E := lambdaSequence Y
    refine image_eq_of_heq rfl ?_ (shiftedLambdaDifferential_heq Y a r p)
      ?_ (E.B_succ r (affineWeight a p) hr)
    · simp only [shiftedLambdaPreSequence, lambdaSequence_first, lambdaSequence_degree,
        affineWeight_add_degree]
    · change HEq
        (boundarySuccessorImage (E.ssData (affineWeight a (p+(r,r-1,0))))
          (r-2).toNat)
        (boundarySuccessorImage (E.ssData (affineWeight a p+E.diffDeg r))
          (r-E.r₀).toNat)
      exact dependent_apply_heq
        (fun q => boundarySuccessorImage (E.ssData q) (r-2).toNat)
        (affineWeight_add_degree a r p)

private theorem shiftedLambdaSequence_first (Y : Syn) (a : ℤ) :
    (shiftedLambdaSequence Y a).r₀ = 2 := rfl

private theorem shiftedLambdaSequence_degree (Y : Syn) (a r : ℤ) :
    (shiftedLambdaSequence Y a).diffDeg r = (r,r-1,0) := rfl

end
end KIP126.Literature.BocksteinRaw
end

@[expose] section
namespace KIP126.Literature.Paper38ComparisonInput
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Literature.BocksteinRaw KIP126.Literature.Paper38OriginalSuccessor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000
set_option Elab.async false

private abbrev fixedShiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum).Additive :=
  background.exactness.shiftAdditive p
private abbrev fixedShiftCommShift (p : ℤ × ℤ) :
    (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum).CommShift ℤ :=
  background.exactness.shiftCommShift p
attribute [local instance] fixedShiftAdditive fixedShiftCommShift
private abbrev fixedShiftTriangulated (p : ℤ × ℤ) :
    (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum).IsTriangulated :=
  background.exactness.shiftExact p
attribute [local instance] fixedShiftTriangulated

/-- The zero-shift synthetic object associated to a spectrum. -/
private abbrev nuZeroSpectrum (X : Spectrum) : SyntheticSpectrum :=
  (SyntheticCategory.biShift (0,0)).obj (background.nu.functor.obj X)

private abbrev source (X : Spectrum) (a : ℤ) :=
  (background.family.obj ((SyntheticCategory.biShift (0,a)).obj (background.nu.functor.obj X))).sequence

/-- Weight-coordinate reindexing on the finite quotient `nuZeroSpectrum X`. -/
private abbrev target (X : Spectrum) (a : ℤ) :=
  shiftedLambdaSequence (nuZeroSpectrum X) a

private def lambdaSS (X : Spectrum) : SyntheticAdamsSS where
  sequence := lambdaSequence (nuZeroSpectrum X)
  firstPage := lambdaSequence_first _
  differentialDegree := lambdaSequence_degree _

private def initialQuotientIso (X : Spectrum) (a s t : ℤ) (k : ℕ) :
    (target X a).Page 2 (s,t,t+a-k) ≅
      ModuleCat.of ℤ (BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) 1)) := by
  change (lambdaSequence (nuZeroSpectrum X)).Page 2 (affineWeight a (s,t,t+a-k)) ≅ _
  exact lambdaInitialQuotientIso background.quotients.coherence (nuZeroSpectrum X)
    (affineWeight a (s,t,t+a-k)) k (by dsimp [affineWeight]; omega)

private def baseInitialQuotientIso (X : Spectrum) (s t : ℤ) (k : ℕ) :
    (lambdaSS X).Page 2 (s,t,t-k) ≅
      ModuleCat.of ℤ (BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) 1)) := by
  change (lambdaSequence (nuZeroSpectrum X)).Page 2 (s,t,t-k) ≅ _
  exact lambdaInitialQuotientIso background.quotients.coherence (nuZeroSpectrum X)
    (s,t,t-k) k (by dsimp; omega)

private def selectedE2Label (X : AdamsObject (coefficients := background.coefficients)) (a s t : ℤ) (k : ℕ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    (source (X.obj background.auxiliary) a).Page 2 (s,t,t+a-k) :=
  background.comparison.nuE2 X a s t k x

private def initialQuotientValue (X : Spectrum) (a s t : ℤ) (k : ℕ)
    (z : (target X a).Page 2 (s,t,t+a-k)) :
    BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) 1) :=
  (initialQuotientIso X a s t k).hom z

private def SelectedE2Calibration
    (first : ∀ (X : Spectrum) (s t : ℤ),
      (background.classical.obj X).Page 2 (s,t) ≃ₗ[ℤ]
        BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) 1))
    (f : ∀ (X : Spectrum) (a : ℤ), FromFirstMorphism (source X a) (target X a)) : Prop :=
  ∀ (X : AdamsObject (coefficients := background.coefficients)) (a s t : ℤ) (k : ℕ)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)),
    initialQuotientValue (X.obj background.auxiliary) a s t k
      ((f (X.obj background.auxiliary) a).pageMap 2 (s,t,t+a-k)
        (selectedE2Label X a s t k x)) = first (X.obj background.auxiliary) s t x

/-- Comparison of the classical and lambda-tower spectral sequences for
all spectra. The lambda differential comes from the lambda tower; the two
effective maps are inverse on E₂. The same SSData maps induce inverse maps
on later pages and at infinity. -/
private structure ComparisonData where
  classicalFirst : ∀ (X : Spectrum) (s t : ℤ),
    (background.classical.obj X).Page 2 (s,t) ≃ₗ[ℤ]
      BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) 1)
  hom : ∀ (X : Spectrum) (a : ℤ), FromFirstMorphism (source X a) (target X a)
  inv : ∀ (X : Spectrum) (a : ℤ), FromFirstMorphism (target X a) (source X a)
  hom_inv_id_e2 : ∀ (X : Spectrum) (a : ℤ) (p : Tridegree),
    (hom X a).pageMap 2 p ≫ (inv X a).pageMap 2 p = 𝟙 _
  inv_hom_id_e2 : ∀ (X : Spectrum) (a : ℤ) (p : Tridegree),
    (inv X a).pageMap 2 p ≫ (hom X a).pageMap 2 p = 𝟙 _
  classicalFirst_selected : ∀ (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)),
    classicalFirst (X.obj background.auxiliary) s t x = firstLabel background X s t x
  e2_selected : SelectedE2Calibration classicalFirst hom
  classical_differential : ∀ (X : Spectrum) (s t : ℤ) (r k : ℕ), 2 ≤ r →
    ∀ (x : (background.classical.obj X).Page 2 (s,t))
      (y : (background.classical.obj X).Page 2 (s+r,t+r-1)),
    HasDifferential (background.classical.obj X) r (s,t) (s+r,t+r-1) x y ↔
      SyntheticHasDifferential (lambdaSS X) r
        (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1) : ℕ))
        ((baseInitialQuotientIso X s t k).inv (classicalFirst X s t x))
        ((baseInitialQuotientIso X (s+r) (t+r-1) (k+(r-1))).inv
          (classicalFirst X (s+r) (t+r-1) y))

/-- External input: the actual all-spectrum Adams--lambda comparison,
with full integer object shifts and the selected-object E2 labels. -/
private theorem adamsLambdaComparison_input : Nonempty ComparisonData := by
  sorry

private def comparisonData : ComparisonData :=
  Classical.choice adamsLambdaComparison_input

end
end KIP126.Literature.Paper38ComparisonInput
end
@[expose] section
namespace KIP126.Literature.Paper38ComparisonInput
open CategoryTheory CategoryTheory.Limits
open KIP126.Core KIP126.Core.SpectralSequence
open KIP126.Literature.Paper38OriginalSuccessor
universe v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem ssData_pageMap_eq_id_of_early
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D : ι → SSData (ModuleCat.{v} ℤ)}
    (f : SSDataMorphism ι D D) (p : ι) (n m : WithTop ℕ) (hnm : n ≤ m)
    (h : f.pageMap p n = 𝟙 _) :
    f.pageMap p m = 𝟙 _ := by
  letI : Epi ((D p).pageπ m) := by
    unfold SSData.pageπ
    infer_instance
  apply (cancel_epi ((D p).pageπ m)).1
  rw [f.pageπ_pageMap, Category.comp_id]
  ext z
  apply (D p).page_eq_of_early_page_eq n m hnm (f.cycleMap p m z) z
  let i := Subobject.ofLE ((D p).Z m) ((D p).Z n) ((D p).Z_anti hnm)
  have hi : f.cycleMap p m ≫ i ≫ (D p).pageπ n = i ≫ (D p).pageπ n := by
    rw [← Category.assoc, ← f.cycleMap_ofLE p hnm, Category.assoc,
      ← f.pageπ_pageMap p n, h, Category.comp_id]
  exact congrArg (fun q => q z) hi

/-- Initial-page inverse laws propagate through the original nested cycle
and boundary quotients to every later page. -/
private theorem fromFirst_pageMap_comp_eq_id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E F : SpectralSequence (ModuleCat.{v} ℤ) ι}
    (f : FromFirstMorphism E F) (g : FromFirstMorphism F E)
    (r : ℤ) (hr : 2 ≤ r) (p : ι)
    (h : f.pageMap 2 p ≫ g.pageMap 2 p = 𝟙 _) :
    f.pageMap r p ≫ g.pageMap r p = 𝟙 _ := by
  let c := f.toSSDataMorphism.comp g.toSSDataMorphism
  have hc : c.pageMapAt (E := E.toPreSS) (E' := E.toPreSS)
      (f.r₀_eq.trans g.r₀_eq) 2 p = 𝟙 _ := by
    rw [SSDataMorphism.pageMapAt_comp]
    exact h
  have hc' : c.pageMap p (↑(2-E.r₀).toNat : WithTop ℕ) = 𝟙 _ := by
    simpa only [SSDataMorphism.pageMapAt, eqToHom_refl, Category.comp_id] using hc
  have hle : (↑(2-E.r₀).toNat : WithTop ℕ) ≤ ↑(r-E.r₀).toNat := by
    exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
  have hcr := ssData_pageMap_eq_id_of_early c p
    (↑(2-E.r₀).toNat : WithTop ℕ) (↑(r-E.r₀).toNat : WithTop ℕ) hle hc'
  have hcr' : c.pageMapAt (E := E.toPreSS) (E' := E.toPreSS)
      (f.r₀_eq.trans g.r₀_eq) r p = 𝟙 _ := by
    simpa only [SSDataMorphism.pageMapAt, eqToHom_refl, Category.comp_id] using hcr
  rw [SSDataMorphism.pageMapAt_comp] at hcr'
  exact hcr'

/-- The SSData maps on infinity quotients are inverse, by the initial-page
inverse law applied to common infinity-cycle representatives. -/
private theorem fromFirst_pageMap_top_comp_eq_id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E F : SpectralSequence (ModuleCat.{v} ℤ) ι}
    (f : FromFirstMorphism E F) (g : FromFirstMorphism F E) (p : ι)
    (h : f.pageMap 2 p ≫ g.pageMap 2 p = 𝟙 _) :
    f.toSSDataMorphism.pageMap p ⊤ ≫ g.toSSDataMorphism.pageMap p ⊤ = 𝟙 _ := by
  let c := f.toSSDataMorphism.comp g.toSSDataMorphism
  have hc : c.pageMapAt (E := E.toPreSS) (E' := E.toPreSS)
      (f.r₀_eq.trans g.r₀_eq) 2 p = 𝟙 _ := by
    rw [SSDataMorphism.pageMapAt_comp]
    exact h
  have hc' : c.pageMap p (↑(2-E.r₀).toNat : WithTop ℕ) = 𝟙 _ := by
    simpa only [SSDataMorphism.pageMapAt, eqToHom_refl, Category.comp_id] using hc
  simpa only [c, SSDataMorphism.pageMap_comp] using
    ssData_pageMap_eq_id_of_early c p (↑(2-E.r₀).toNat : WithTop ℕ) ⊤ le_top hc'

end
end KIP126.Literature.Paper38ComparisonInput
end

@[expose] section
namespace KIP126.Literature.Paper38ComparisonInput
open CategoryTheory CategoryTheory.Limits
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic.Completed
open KIP126.Synthetic.SpectralSequence
open KIP126.Literature.Paper38OriginalSuccessor KIP126.Literature.Paper38Successor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000
set_option Elab.async false

private theorem source_first (X : Spectrum) (a : ℤ) : (source X a).r₀ = 2 :=
  background.family.firstPage _

/-- The later-page inverse identity follows from the E2 field. -/
private theorem ComparisonData.hom_inv_id (C : ComparisonData)
    (X : Spectrum) (a r : ℤ) (hr : 2 ≤ r) (p : Tridegree) :
    (C.hom X a).pageMap r p ≫ (C.inv X a).pageMap r p = 𝟙 _ :=
  fromFirst_pageMap_comp_eq_id (C.hom X a) (C.inv X a) r hr p (C.hom_inv_id_e2 X a p)

/-- The reverse later-page inverse identity uses the same initial-page law. -/
private theorem ComparisonData.inv_hom_id (C : ComparisonData)
    (X : Spectrum) (a r : ℤ) (hr : 2 ≤ r) (p : Tridegree) :
    (C.inv X a).pageMap r p ≫ (C.hom X a).pageMap r p = 𝟙 _ :=
  fromFirst_pageMap_comp_eq_id (C.inv X a) (C.hom X a) r hr p (C.inv_hom_id_e2 X a p)

/-- The comparison uses inverse maps on every valid original page. -/
private def comparisonPageIso (X : Spectrum) (a r : ℤ) (hr : 2 ≤ r) (p : Tridegree) :
    (source X a).Page r p ≅ (target X a).Page r p where
  hom := (comparisonData.hom X a).pageMap r p
  inv := (comparisonData.inv X a).pageMap r p
  hom_inv_id := comparisonData.hom_inv_id X a r hr p
  inv_hom_id := comparisonData.inv_hom_id X a r hr p

/-- The same ambient maps also give inverse maps on the original infinity
quotients, using the initial-page inverse laws. -/
private def comparisonInfinityIso (X : Spectrum) (a : ℤ) (p : Tridegree) :
    ((source X a).ssData p).eInfty ≅ ((target X a).ssData p).eInfty where
  hom := (comparisonData.hom X a).toSSDataMorphism.pageMap p ⊤
  inv := (comparisonData.inv X a).toSSDataMorphism.pageMap p ⊤
  hom_inv_id := fromFirst_pageMap_top_comp_eq_id
    (comparisonData.hom X a) (comparisonData.inv X a) p
    (comparisonData.hom_inv_id_e2 X a p)
  inv_hom_id := fromFirst_pageMap_top_comp_eq_id
    (comparisonData.inv X a) (comparisonData.hom X a) p
    (comparisonData.inv_hom_id_e2 X a p)

/-- The successor is the canonical successor of each original spectral
sequence, with its map induced by the same effective comparison. -/
private theorem comparison_successor_hom (X : Spectrum) (a r : ℤ) (hr : 2 ≤ r)
    (p : Tridegree) :
    (pageHomologyIso (source X a) r p (by rw [source_first]; exact hr)).hom ≫
        centeredHomologyMap (comparisonData.hom X a) r p
          (by rw [source_first]; exact hr) =
      (comparisonData.hom X a).pageMap (r+1) p ≫
        (pageHomologyIso (target X a) r p (by exact hr)).hom :=
  canonicalSuccessor_naturality (comparisonData.hom X a) r p
    (by rw [source_first]; exact hr)

private theorem comparison_successor_inv (X : Spectrum) (a r : ℤ) (hr : 2 ≤ r)
    (p : Tridegree) :
    (pageHomologyIso (target X a) r p (by exact hr)).hom ≫
        centeredHomologyMap (comparisonData.inv X a) r p (by exact hr) =
      (comparisonData.inv X a).pageMap (r+1) p ≫
        (pageHomologyIso (source X a) r p (by rw [source_first]; exact hr)).hom :=
  canonicalSuccessor_naturality (comparisonData.inv X a) r p (by exact hr)

end
end KIP126.Literature.Paper38ComparisonInput
end
