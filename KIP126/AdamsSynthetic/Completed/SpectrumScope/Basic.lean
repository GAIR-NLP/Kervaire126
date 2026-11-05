module

public import KIP126.AdamsSynthetic.Completed

/-! AimPaper's domain and suspension-stable enlargement in the HF₂-local category. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.Kervaire.Route
noncomputable section

/-- AimPaper §2: completed, connective spectra of degreewise finite mod-two type.
Completion is expressed by membership in the fixed HF₂-local category. -/
public def IsPaperSpectrum (X : Spectrum) : Prop :=
  IsConnective X ∧ IsFiniteModTwoType coefficients X

/-- The paper's full object range. -/
public abbrev PaperSpectrum := {X : Spectrum // IsPaperSpectrum X}

/-- Arbitrary bounded-below finite-type spectra, allowing integer suspensions. -/
public abbrev AdamsSpectrum := {X : Spectrum // IsBoundedBelowFiniteModTwoType coefficients X}

public theorem IsPaperSpectrum.isBoundedBelowFiniteModTwoType {X : Spectrum}
    (hX : IsPaperSpectrum X) : IsBoundedBelowFiniteModTwoType coefficients X :=
  ⟨hX.1.isBoundedBelow, hX.2⟩

/-- The index interprets to this very spectrum, with no selected-object proxy. -/
public def PaperSpectrum.adamsObject (X : PaperSpectrum) : AdamsObject (coefficients := coefficients) :=
  .spectrum X.val X.property.isBoundedBelowFiniteModTwoType

public instance : Coe PaperSpectrum (AdamsObject (coefficients := coefficients)) :=
  ⟨PaperSpectrum.adamsObject⟩

public def AdamsSpectrum.adamsObject (X : AdamsSpectrum) : AdamsObject (coefficients := coefficients) :=
  .spectrum X.val X.property

public instance : Coe AdamsSpectrum (AdamsObject (coefficients := coefficients)) :=
  ⟨AdamsSpectrum.adamsObject⟩

public theorem PaperSpectrum.adamsObject_obj (X : PaperSpectrum) :
    X.adamsObject.obj auxiliary = X.val := rfl

public theorem AdamsSpectrum.adamsObject_obj (X : AdamsSpectrum) :
    X.adamsObject.obj auxiliary = X.val := rfl

/-- An actual triangle on arbitrary paper spectra, with its original maps. -/
public def paperTriangleData (T : CategoryTheory.Pretriangulated.Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum)
    (hX : IsPaperSpectrum T.obj₁) (hY : IsPaperSpectrum T.obj₂)
    (hZ : IsPaperSpectrum T.obj₃) : TriangleData auxiliary where
  X := .spectrum T.obj₁ hX.isBoundedBelowFiniteModTwoType
  Y := .spectrum T.obj₂ hY.isBoundedBelowFiniteModTwoType
  Z := .spectrum T.obj₃ hZ.isBoundedBelowFiniteModTwoType
  f := T.mor₁
  g := T.mor₂
  h := T.mor₃
  distinguished := hT

/-- Connectivity of the completed sphere. -/
public theorem sphere_isPaperSpectrum : IsPaperSpectrum sphere := by sorry

/-- Connectivity of the completed Hopf cofiber. -/
public theorem nuCofiber_isPaperSpectrum :
    IsPaperSpectrum (ClassicalObject.nuCofiber.obj auxiliary) := by sorry

/-- The completed pointed detector is a connective finite-mod-two-type spectrum. -/
public theorem detector_isPaperSpectrum : IsPaperSpectrum auxiliary.detector := by sorry

public def paperSphere : PaperSpectrum := ⟨sphere, sphere_isPaperSpectrum⟩
public def paperNuCofiber : PaperSpectrum :=
  ⟨ClassicalObject.nuCofiber.obj auxiliary, nuCofiber_isPaperSpectrum⟩
public def paperDetector : PaperSpectrum := ⟨auxiliary.detector, detector_isPaperSpectrum⟩

end
end KIP126.AdamsSynthetic.Completed
