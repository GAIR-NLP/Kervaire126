module

public import KIP126.AdamsSynthetic.Completed.Completion.Classical
public import KIP126.AdamsSynthetic.AdamsBackground
public import KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Completed.Coefficients

/-! The classical and synthetic Adams constructions on the completed categories.
The public objects are projections of the same selected construction data.
The E₂ and first-quotient comparisons are chosen together with synthetic
convergence and their detection laws.
-/

@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory.MonoidalCategory
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route
noncomputable section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-- The fixed auxiliary spectra used in the selected object closure. -/
public def auxiliary : AuxiliaryData Spectrum (coefficients := coefficients) where
  etaMap := (completionSphereShiftIso 1).inv ≫ completion.map Ordinary.auxiliary.etaMap ≫ completionSphereIso.hom
  nuMap := (completionSphereShiftIso 3).inv ≫ completion.map Ordinary.auxiliary.nuMap ≫ completionSphereIso.hom
  detector := completion.obj Ordinary.auxiliary.detector
  detectorUnit := completionSphereIso.inv ≫ completion.map Ordinary.auxiliary.detectorUnit

private structure ClassicalAdamsData where
  classical : ClassicalAdamsFamily Spectrum
  classicalTower : ClassicalTowerPresentation coefficients.unit classical
  classicalSuspension (X : AdamsObject) :
    ClassicalTowerSuspension classicalTower (X.obj auxiliary)

private def classicalAdamsConstruction : ClassicalAdamsData where
  classical := by sorry
  classicalTower := by sorry
  classicalSuspension := by sorry

/-- The classical Adams functor, including its first page and differential degree. -/
public def classical : ClassicalAdamsFamily Spectrum := classicalAdamsConstruction.classical

/-- The tower presentation of this very classical family. -/
public def classicalTower : ClassicalTowerPresentation coefficients.unit classical :=
  classicalAdamsConstruction.classicalTower

public def classicalSuspension (X : AdamsObject) :
    ClassicalTowerSuspension classicalTower (X.obj auxiliary) :=
  classicalAdamsConstruction.classicalSuspension X

private structure SyntheticContextData where
  nu : NuFunctorData Spectrum SyntheticSpectrum
  nu_preserves_triangle (T : CategoryTheory.Pretriangulated.Triangle Spectrum)
      (hT : T ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients T) :
    ∃ h : nu.functor.obj T.obj₃ ⟶
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).obj (nu.functor.obj T.obj₁),
      CategoryTheory.Pretriangulated.Triangle.mk
        (nu.functor.map T.mor₁) (nu.functor.map T.mor₂) h ∈ distTriang SyntheticSpectrum
  recovery : LambdaRecovery nu
  exactness : StructuralExactness nu recovery

private def syntheticContextConstruction : SyntheticContextData where
  nu := by sorry
  nu_preserves_triangle := by sorry
  recovery := by sorry
  exactness := by sorry

/-- The fixed ν functor, including its sphere and suspension comparisons. -/
public def nu : NuFunctorData Spectrum SyntheticSpectrum := syntheticContextConstruction.nu

/-- ν preserves a distinguished triangle under the complete HF₂ short-exactness hypothesis. -/
public theorem nu_preserves_triangle (T : CategoryTheory.Pretriangulated.Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients T) :
    ∃ h : nu.functor.obj T.obj₃ ⟶
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).obj (nu.functor.obj T.obj₁),
      CategoryTheory.Pretriangulated.Triangle.mk
        (nu.functor.map T.mor₁) (nu.functor.map T.mor₂) h ∈ distTriang SyntheticSpectrum :=
  syntheticContextConstruction.nu_preserves_triangle T hT hH

/-- The λ-localization and its equivalence with this classical category. -/
public def recovery : LambdaRecovery nu := syntheticContextConstruction.recovery

/-- Exactness for the same shifts, ν, and realization. -/
public def exactness : StructuralExactness nu recovery := syntheticContextConstruction.exactness

private structure SyntheticAdamsData where
  family : SyntheticAdamsFamily SyntheticSpectrum
  syntheticTower : SyntheticTowerPresentation (nuCoefficientUnit coefficients nu) family

private def syntheticAdamsConstruction : SyntheticAdamsData where
  family := by sorry
  syntheticTower := by sorry

/-- The synthetic Adams functor on the fixed synthetic category. -/
public def family : SyntheticAdamsFamily SyntheticSpectrum := syntheticAdamsConstruction.family

/-- Its tower uses the image under this ν of the same HF₂ coefficient unit. -/
public def syntheticTower : SyntheticTowerPresentation (nuCoefficientUnit coefficients nu) family :=
  syntheticAdamsConstruction.syntheticTower

/-- The finite λ quotient system uses the same jointly chosen synthetic
cofibers, including their specified maps and restriction squares. -/
public def quotients : LambdaQuotientSystem SyntheticSpectrum :=
  syntheticQuotientConstruction.quotients

private structure AdamsComparisonData where
  convergence (X : SyntheticObject) :
    SyntheticTowerConvergence syntheticTower (X.obj nu auxiliary)
  comparison : E2Comparison classical family nu auxiliary
  normalizedMap (X Y : AdamsObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary) :
    NormalizedSyntheticMap classicalTower nu f
  firstQuotient : FirstQuotientComparison classical nu auxiliary
  first_quotient : ∀ (X : AdamsObject) (a s t : ℤ)
      (x : (classical.obj (X.obj auxiliary)).Page 2 (s,t)),
    KIP126.AdamsSynthetic.Detects
      (convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
      (family.pageMap
        (HasFunctorialCofiber.cofibι (lambdaPow 1
          ((SyntheticCategory.biShift (0,a)).obj (nu.functor.obj (X.obj auxiliary)))))
        2 (s,t,t+a) (by simpa only [Nat.cast_zero, sub_zero] using comparison.nuE2 X a s t 0 x))
      ((firstQuotient X a s t).symm x)
  sphere_homotopy_lambda : ∀ (s t : ℤ) (k : ℕ)
      (x : BiHom (t-s) t (S_0_0 : SyntheticSpectrum)),
    Detects (convergence .sphere) (s,t,t-k)
      (comparison.sphereE2 s t k
        (sphereFirstQuotient nu quotients.functoriality firstQuotient s t (quotientClass 1 x)))
      (lambdaMultiply k x)

private def adamsComparisonConstruction : AdamsComparisonData where
  convergence := by sorry
  comparison := by sorry
  normalizedMap := by sorry
  firstQuotient := by sorry
  first_quotient := by sorry
  sphere_homotopy_lambda := by sorry

public def comparison : E2Comparison classical family nu auxiliary :=
  adamsComparisonConstruction.comparison

public def normalizedMap (X Y : AdamsObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary) :
    NormalizedSyntheticMap classicalTower nu f :=
  adamsComparisonConstruction.normalizedMap X Y f

public def firstQuotient : FirstQuotientComparison classical nu auxiliary :=
  adamsComparisonConstruction.firstQuotient

end
end KIP126.AdamsSynthetic.Completed
