module

public import KIP126.AdamsSynthetic.Completed.Background
public import KIP126.AdamsSynthetic.AdamsFiltration
import KIP126.AdamsSynthetic.Completed.Filtration
import all KIP126.AdamsSynthetic.Internal.SphereConvergence.Tower

/-! Support properties of the fixed classical Adams system. -/
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.Kervaire.Route KIP126.StableHomotopy

private theorem page_subsingleton_of_ambient
    (D : KIP126.Core.SpectralSequence.SSData (ModuleCat.{0} ℤ))
    (r : WithTop ℕ) [Subsingleton D.V] : Subsingleton (D.page r) := by
  have hV : IsZero D.V := ModuleCat.isZero_of_subsingleton D.V
  have hZ : IsZero (Subobject.underlying.obj (D.Z r)) :=
    IsZero.of_mono (D.Z r).arrow hV
  letI : Epi (D.pageπ r) := coequalizer.π_epi
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_epi (D.pageπ r) hZ)

public theorem classical_page_negative (X : AdamsObject) (r s t : ℤ)
    (hs : s < 0) :
    Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page r (s,t)) := by
  let T := background.classicalTower.tower (X.obj background.auxiliary)
  have hi (a b : ℕ) (hab : a ≤ b) (h : a = b) : IsIso (T.map hab) := by
    subst b
    rw [T.map_self]
    infer_instance
  let f := T.mapAt (show s ≤ s+1 by omega)
  haveI : IsIso f := hi s.toNat (s+1).toNat (by omega) (by omega)
  have hLayer : IsZero (T.layer s) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      (Pretriangulated.Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f))
      (HasFunctorialCofiber.cofib_distinguished f) (show IsIso f from inferInstance)
  letI : Subsingleton (T.FirstPage (s,t)) := ⟨fun a b => hLayer.eq_of_tgt a b⟩
  let D := (background.classical.obj (X.obj background.auxiliary)).ssData (s,t)
  letI : Subsingleton D.V :=
    (background.classicalTower.sequence (X.obj background.auxiliary)).ambient (s,t)
      |>.toLinearEquiv.injective.subsingleton
  exact page_subsingleton_of_ambient D _

public theorem sphere_page_filtration_zero (r : ℤ) (t : ℕ) (ht : t ≠ 0) :
    Subsingleton (background.classical.sphere.Page r (0,t)) := by
  let T := background.classicalTower.tower (SphereSpectrum (C := Spectrum))
  let e : T.layer 0 ≅ background.coefficients.object :=
    T.layerIso 0 ≪≫ (tensorLeft background.coefficients.object).mapIso T.zeroIso ≪≫
      ρ_ background.coefficients.object
  letI := background.coefficients.homotopy_vanishes (t : ℤ) (by exact_mod_cast ht)
  letI : Subsingleton (T.FirstPage (0,t)) := by
    change Subsingleton (HomotopyGroup (t : ℤ) (T.layer 0))
    exact (Iso.homCongr (Iso.refl (Sphere (C := Spectrum) (t : ℤ))) e).injective.subsingleton
  let D := background.classical.sphere.ssData (0,t)
  letI : Subsingleton D.V :=
    (background.classicalTower.sequence (SphereSpectrum (C := Spectrum))).ambient (0,t)
      |>.toLinearEquiv.injective.subsingleton
  exact page_subsingleton_of_ambient D _

/-- The odd-torsion consequence of infinite HF₂ Adams filtration on the
completed sphere and its finite cell shifts. The full vanishing
statement is supplied separately by classical_filtration_separated. -/
public theorem classical_sphere_separated (m : ℤ)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ∀ s : ℕ, a ∈ (background.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
    KIP126.AdamsSynthetic.IsOddTorsionMap a := by
  apply finite_map_separation
    (IsFiniteSpectrum.shift m IsFiniteSpectrum.sphere) IsFiniteSpectrum.sphere a
  intro s
  exact ha s.toNat

/-- The argument specializes to the same classical tower.
Its residual-acyclicity and finite-kernel premises are
explicit; neither is obtained from the separation conclusion. -/
private theorem classical_sphere_separated_of_residual_acyclic
    (products : HasProductsOfShape ℕ Spectrum)
    (hacyclic : letI := products;
      IsIso (Internal.SphereConvergence.Tower.oneSubShift
        (background.classicalTower.tower SphereSpectrum)))
    (m : ℤ)
    (hfinite : ∀ s : ℕ, Finite (inducedMap
      ((background.classicalTower.tower SphereSpectrum).map (Nat.le_succ s)) m).ker)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ∀ s : ℕ,
      a ∈ (background.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
    a = 0 := by
  letI := products
  exact Internal.SphereConvergence.Tower.filtration_element_separated
    (background.classicalTower.tower SphereSpectrum) m hfinite
    (Internal.SphereConvergence.Tower.hom_delta_bijective
      (background.classicalTower.tower SphereSpectrum) hacyclic (Sphere m)).injective a ha

end KIP126.AdamsSynthetic.Completed
