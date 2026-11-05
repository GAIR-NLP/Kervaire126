module

public import KIP126.AdamsSynthetic.Completed.SpectrumScope
public import KIP126.AdamsSynthetic.Completed.Filtration
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! The completed mod-two Moore spectrum and its cofiber maps, defined by
multiplication by two on the completed sphere of the Adams calculation. -/

@[expose] section
namespace KIP126.AdamsComputation.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Kervaire.Route
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false

public def twoMap : SphereSpectrum (C := Spectrum) ⟶ SphereSpectrum := 2 • 𝟙 _

public def spectrum : Spectrum := HasFunctorialCofiber.cofib twoMap

public def bottom : SphereSpectrum (C := Spectrum) ⟶ spectrum :=
  HasFunctorialCofiber.cofibι twoMap

public def top : spectrum ⟶ (SphereSpectrum (C := Spectrum))⟦(1 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ twoMap

public def cofiberSequence : HoCofiberSequence (C := Spectrum) where
  X := SphereSpectrum
  Y := SphereSpectrum
  Z := spectrum
  f := twoMap
  g := bottom
  h := top
  distinguished := HasFunctorialCofiber.cofib_distinguished twoMap

public theorem bottom_top : bottom ≫ top = 0 :=
  comp_distTriang_mor_zero₂₃ _ cofiberSequence.distinguished

public theorem top_shift_two : top ≫ (shiftFunctor Spectrum (1 : ℤ)).map twoMap = 0 :=
  comp_distTriang_mor_zero₃₁ _ cofiberSequence.distinguished

public abbrev sequence := background.classical.obj spectrum

public abbrev Page (s t : ℕ) := sequence.Page 2 (s,t)

private theorem desuspend_injective (X : Spectrum) (i : ℤ) :
    Function.Injective (AbstractAdamsTower.desuspend X i) := by
  let e := (shiftFunctorAdd' Spectrum i (-1) (i - 1) (by omega)).app SphereSpectrum
  let d := (shiftFunctorCompIsoId Spectrum 1 (-1) (by omega)).app X
  intro a b h
  change e.hom ≫ (shiftFunctor Spectrum (-1 : ℤ)).map a ≫ d.hom =
    e.hom ≫ (shiftFunctor Spectrum (-1 : ℤ)).map b ≫ d.hom at h
  apply (shiftFunctor Spectrum (-1 : ℤ)).map_injective
  apply (cancel_epi e.hom).mp
  apply (cancel_mono d.hom).mp
  simpa only [Category.assoc] using h

private theorem connective : IsConnective spectrum := by
  intro n hn
  haveI : Subsingleton (HomotopyGroup (C := Spectrum) n SphereSpectrum) :=
    sphere_isPaperSpectrum.1 n hn
  haveI : Subsingleton (HomotopyGroup (C := Spectrum) (n-1) SphereSpectrum) :=
    sphere_isPaperSpectrum.1 (n-1) (by omega)
  have hz (a : HomotopyGroup n spectrum) : a = 0 := by
    have hat : a ≫ top = 0 := by
      apply desuspend_injective SphereSpectrum n
      exact Subsingleton.elim _ _
    obtain ⟨b,hb⟩ := Triangle.coyoneda_exact₃
      (Triangle.mk twoMap bottom top) cofiberSequence.distinguished a hat
    have hb0 : b = 0 := by
      exact (sphere_isPaperSpectrum.1 n hn).elim b 0
    rw [hb, hb0, zero_comp]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

private theorem finite_modTwoHomology : IsFiniteModTwoType coefficients spectrum := by
  intro n
  let f := modTwoHomologyMap coefficients bottom n
  let g := modTwoConnecting coefficients homologyShift cofiberSequence n
  have hfg : Function.Exact f g := homology_exact cofiberSequence n
  let S : ShortComplex AddCommGrpCat := ShortComplex.mk
    (AddCommGrpCat.ofHom f) (AddCommGrpCat.ofHom g) (by
      ext x
      exact (hfg (f x)).2 ⟨x,rfl⟩)
  have hS : S.Exact := S.ab_exact_iff.mpr (by
    intro x hx
    exact (hfg x).1 hx)
  haveI : Finite S.X₁ := sphere_isPaperSpectrum.2 n
  haveI : Finite S.X₃ := sphere_isPaperSpectrum.2 (n-1)
  exact hS.ab_finite

public theorem isPaperSpectrum : IsPaperSpectrum spectrum :=
  ⟨connective, finite_modTwoHomology⟩

public def adamsObject : AdamsObject (coefficients := coefficients) :=
  .spectrum spectrum isPaperSpectrum.isBoundedBelowFiniteModTwoType

public theorem adamsObject_obj : adamsObject.obj background.auxiliary = spectrum := rfl

public def triangle : TriangleData background.auxiliary where
  X := .sphere
  Y := .sphere
  Z := adamsObject
  f := twoMap
  g := bottom
  h := top
  distinguished := cofiberSequence.distinguished

end
end KIP126.AdamsComputation.Moore
