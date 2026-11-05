module
import KIP126.Literature.Standard
import KIP126.AdamsSynthetic.Completed.Filtration
import KIP126.AdamsSynthetic.Completed.SphereCoproduct

@[expose] section
namespace KIP126.Literature.Standard.HUnitCore
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual target coefficient is connective, in the repository convention. -/
private theorem coefficient_connected : IsConnected coefficients.object (-1) := by
  intro n hn
  exact coefficients.homotopy_vanishes n (by omega)

/-- The coefficient smash is connective. -/
private theorem coefficient_square_connected :
    IsConnected (coefficients.object ⊗ coefficients.object) (-1) :=
  connected_homology_vanishing coefficients.object (-1) coefficient_connected

/-- Vanishing from the objectwise universal-coefficient theorem. -/
private theorem hom_coefficient_subsingleton_of_connected
    (X : Spectrum) (hX : IsConnected X 0) : Subsingleton (X ⟶ coefficients.object) := by
  letI : Subsingleton (ModTwoHomology coefficients (-0) X) :=
    connected_homology_vanishing X 0 hX 0 (by omega)
  let e := (shiftFunctorZero Spectrum ℤ).app X
  refine ⟨fun a b => ?_⟩
  apply (cancel_epi e.hom).mp
  apply (universal_coefficient 0 X).injective
  exact Subsingleton.elim _ _

/-- The normalized actual sphere unit surjects on degree zero. -/
private theorem coefficient_unit_pi0_surjective :
    Function.Surjective (inducedMap coefficients.unit 0) := by
  intro a
  have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases htwo (coefficients.pi0Equiv a) with ha | ha
  · refine ⟨0, ?_⟩
    apply coefficients.pi0Equiv.injective
    simpa only [map_zero] using ha.symm
  · refine ⟨(shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum, ?_⟩
    apply coefficients.pi0Equiv.injective
    change coefficients.pi0Equiv
      ((shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫ coefficients.unit) =
      coefficients.pi0Equiv a
    rw [ModTwoCoefficients.unit, ← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp, AddEquiv.apply_symm_apply]
    exact ha.symm

/-- The square has nonzero degree-zero homotopy: otherwise objectwise UCT
    would make the identity of the same coefficient object zero. -/
private theorem coefficient_square_pi0_not_subsingleton :
    ¬ Subsingleton (HomotopyGroup 0 (coefficients.object ⊗ coefficients.object)) := by
  intro hz
  letI : Subsingleton (ModTwoHomology coefficients (-0) coefficients.object) := hz
  have he : Subsingleton (((shiftFunctor Spectrum (0 : ℤ)).obj coefficients.object ⟶ coefficients.object)) :=
    (universal_coefficient 0 coefficients.object).injective.subsingleton
  have hi : (𝟙 coefficients.object) = 0 := by
    apply (cancel_epi ((shiftFunctorZero Spectrum ℤ).hom.app coefficients.object)).mp
    exact he.elim _ _
  have hh := congrArg
    (fun f : coefficients.object ⟶ coefficients.object =>
      coefficients.pi0Equiv (coefficients.pi0Equiv.symm 1 ≫ f)) hi
  have h10 : (1 : ZMod 2) = 0 := by
    simpa only [Category.comp_id, comp_zero, map_zero, AddEquiv.apply_symm_apply] using hh
  exact one_ne_zero h10

private def homSourceEquiv {X Y Z : Spectrum} (e : X ≅ Y) :
    (X ⟶ Z) ≃ (Y ⟶ Z) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp [← Category.assoc]
  right_inv f := by simp [← Category.assoc]

private def homotopyShiftEquiv (Y : Spectrum) (a n : ℤ) :
    HomotopyGroup n (Y⟦a⟧) ≃ HomotopyGroup (n-a) Y := by
  let E := shiftEquiv' Spectrum (-a) a (by omega)
  let e := (E.toAdjunction.homEquiv (Sphere (C := Spectrum) n) Y).symm
  exact e.trans (homSourceEquiv
    ((shiftFunctorAdd' Spectrum n (-a) (n-a) (by omega)).symm.app SphereSpectrum))

/-- The exact connectivity step needed for the actual sphere evaluation cover. -/
private theorem triangle_cover_connected
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hA : IsConnected T.obj₁ (-1)) (hX : IsConnected T.obj₂ (-1))
    (h0 : Function.Surjective (inducedMap T.mor₁ 0)) : IsConnected T.obj₃ 0 := by
  intro n hn
  letI : Subsingleton (HomotopyGroup (n-1) T.obj₁) := hA (n-1) (by omega)
  letI : Subsingleton (HomotopyGroup n (T.obj₁⟦(1 : ℤ)⟧)) :=
    (homotopyShiftEquiv T.obj₁ 1 n).injective.subsingleton
  have hz (a : HomotopyGroup n T.obj₃) : a = 0 := by
    obtain ⟨b, hb⟩ := T.coyoneda_exact₃ hT a (Subsingleton.elim _ _)
    by_cases h : n = 0
    · subst n
      obtain ⟨c,hc⟩ := h0 b
      change c ≫ T.mor₁ = b at hc
      rw [hb, ← hc, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
    · have hb0 : b = 0 := (hX n (by omega)).elim _ _
      rw [hb, hb0, zero_comp]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Equality on the generators of a connective cover detects maps to HF₂. -/
private theorem coefficient_map_eq_of_cover
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hA : IsConnected T.obj₁ (-1)) (hX : IsConnected T.obj₂ (-1))
    (h0 : Function.Surjective (inducedMap T.mor₁ 0))
    (f g : T.obj₂ ⟶ coefficients.object) (hfg : T.mor₁ ≫ f = T.mor₁ ≫ g) :
    f = g := by
  have hC := hom_coefficient_subsingleton_of_connected T.obj₃
    (triangle_cover_connected T hT hA hX h0)
  apply sub_eq_zero.mp
  obtain ⟨b,hb⟩ := T.yoneda_exact₂ hT (f-g) (by
    rw [Preadditive.comp_sub, hfg, sub_self])
  rw [hC.elim b 0, comp_zero] at hb
  exact hb

private theorem coefficient_map_eq_of_sphere_coproduct
    (X : Spectrum)
    [HasCoproduct (fun _ : HomotopyGroup 0 X => Sphere (C := Spectrum) 0)]
    (hA : IsConnected (∐ fun _ : HomotopyGroup 0 X => Sphere (C := Spectrum) 0) (-1))
    (hX : IsConnected X (-1))
    (f g : X ⟶ coefficients.object)
    (hfg : inducedMap f 0 = inducedMap g 0) : f = g := by
  let A (_ : HomotopyGroup 0 X) := Sphere (C := Spectrum) 0
  let e : (∐ A) ⟶ X := Sigma.desc (fun a : HomotopyGroup 0 X => a)
  let T := Triangle.mk e (HasFunctorialCofiber.cofibι e)
    (HasFunctorialCofiber.cofibδ e)
  have hT : T ∈ distTriang Spectrum := HasFunctorialCofiber.cofib_distinguished e
  apply coefficient_map_eq_of_cover T hT hA hX
  · intro a
    refine ⟨Sigma.ι A a, ?_⟩
    change Sigma.ι A a ≫ Sigma.desc _ = a
    exact Sigma.ι_desc _ _
  · apply Sigma.hom_ext
    intro a
    change Sigma.ι A a ≫ e ≫ f = Sigma.ι A a ≫ e ≫ g
    dsimp only [e]
    simp only [Sigma.ι_desc_assoc]
    exact congrArg (fun k : HomotopyGroup 0 X →+ HomotopyGroup 0 coefficients.object => k a) hfg

private def coefficientSelfUnit : coefficients.object ⟶ coefficients.object ⊗ coefficients.object :=
  (λ_ coefficients.object).inv ≫ coefficients.unit ▷ coefficients.object

/-- The actual coefficient-unit map is surjective on π₀. The cofiber of
    S→H is 1-connected, so its right H-tensor has zero degree-zero homotopy. -/
private theorem coefficientSelfUnit_pi0_surjective :
    Function.Surjective (inducedMap coefficientSelfUnit 0) := by
  let H := coefficients.object
  let C := HasFunctorialCofiber.cofib coefficients.unit
  let T := Triangle.mk coefficients.unit (HasFunctorialCofiber.cofibι coefficients.unit)
    (HasFunctorialCofiber.cofibδ coefficients.unit)
  have hT : T ∈ distTriang Spectrum := HasFunctorialCofiber.cofib_distinguished _
  have hC : IsConnected C 0 := triangle_cover_connected T hT sphere_connected
    coefficient_connected coefficient_unit_pi0_surjective
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift H
  letI := closedBackground.tensorExact H
  let F := tensorRight H
  let U := F.mapTriangle.obj T
  have hU : U ∈ distTriang Spectrum := F.map_distinguished T hT
  have hz : Subsingleton (HomotopyGroup 0 U.obj₃) := by
    have hHC := connected_homology_vanishing C 0 hC 0 (by omega)
    refine ⟨fun a b => ?_⟩
    apply (cancel_mono (β_ C H).hom).mp
    exact hHC.elim _ _
  intro a
  obtain ⟨b,hb⟩ := U.coyoneda_exact₂ hU a (hz.elim _ _)
  refine ⟨b ≫ (λ_ H).hom, ?_⟩
  change (b ≫ (λ_ H).hom) ≫ ((λ_ H).inv ≫ coefficients.unit ▷ H) = a
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hb.symm

/-- The degree-zero map is injective: its domain has two elements and
its codomain is nonzero. -/
private theorem coefficientSelfUnit_pi0_injective :
    Function.Injective (inducedMap coefficientSelfUnit 0) := by
  let f := inducedMap coefficientSelfUnit 0
  have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  apply (injective_iff_map_eq_zero f).mpr
  intro a ha
  rcases htwo (coefficients.pi0Equiv a) with ha0 | ha1
  · apply coefficients.pi0Equiv.injective
    simpa only [map_zero] using ha0
  · exfalso
    apply coefficient_square_pi0_not_subsingleton
    have hz : ∀ b, f b = 0 := by
      intro b
      rcases htwo (coefficients.pi0Equiv b) with hb0 | hb1
      · have hb : b = 0 := coefficients.pi0Equiv.injective (by
          simpa only [map_zero] using hb0)
        rw [hb, map_zero]
      · have hb : b = a := coefficients.pi0Equiv.injective (hb1.trans ha1.symm)
        exact hb ▸ ha
    have hz' : ∀ b : HomotopyGroup 0 (coefficients.object ⊗ coefficients.object), b = 0 := by
      intro b
      obtain ⟨a, rfl⟩ := coefficientSelfUnit_pi0_surjective b
      exact hz a
    exact ⟨fun a b => (hz' a).trans (hz' b).symm⟩

/-- A unit retraction follows from connectivity of the sphere coproduct
covering the specified fiber. -/
private theorem coefficientSelfUnit_retraction_of_sphere_coproduct
    [HasCoproduct (fun _ : HomotopyGroup 0
      ((HasFunctorialCofiber.cofib coefficientSelfUnit)⟦(-1 : ℤ)⟧) =>
        Sphere (C := Spectrum) 0)]
    (hA : IsConnected (∐ fun _ : HomotopyGroup 0
      ((HasFunctorialCofiber.cofib coefficientSelfUnit)⟦(-1 : ℤ)⟧) =>
        Sphere (C := Spectrum) 0) (-1)) :
    ∃ μ : coefficients.object ⊗ coefficients.object ⟶ coefficients.object,
      coefficientSelfUnit ≫ μ = 𝟙 coefficients.object := by
  let C := HasFunctorialCofiber.cofib coefficientSelfUnit
  let T := Triangle.mk coefficientSelfUnit (HasFunctorialCofiber.cofibι coefficientSelfUnit)
    (HasFunctorialCofiber.cofibδ coefficientSelfUnit)
  have hT : T ∈ distTriang Spectrum := HasFunctorialCofiber.cofib_distinguished _
  have hC : IsConnected C 0 := triangle_cover_connected T hT coefficient_connected
    coefficient_square_connected coefficientSelfUnit_pi0_surjective
  have hF : IsConnected T.invRotate.obj₁ (-1) := by
    intro n hn
    letI := hC (n - (-1)) (by omega)
    exact (homotopyShiftEquiv C (-1) n).injective.subsingleton
  have hU := inv_rot_of_distTriang T hT
  have hi : T.invRotate.mor₁ = 0 := by
    apply coefficient_map_eq_of_sphere_coproduct
      ((HasFunctorialCofiber.cofib coefficientSelfUnit)⟦(-1 : ℤ)⟧) hA hF
    ext a
    apply coefficientSelfUnit_pi0_injective
    change (a ≫ T.invRotate.mor₁) ≫ T.invRotate.mor₂ = (a ≫ 0) ≫ T.invRotate.mor₂
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ _ hU, comp_zero, comp_zero, zero_comp]
  obtain ⟨μ,hμ⟩ := T.invRotate.yoneda_exact₂ hU (𝟙 coefficients.object) (by rw [hi, zero_comp])
  exact ⟨μ,hμ.symm⟩

/-- The fixed HF₂ unit retraction obtained from the sphere coproduct and
its connectivity theorem. -/
private theorem coefficientSelfUnit_retraction :
    ∃ μ : coefficients.object ⊗ coefficients.object ⟶ coefficients.object,
      coefficientSelfUnit ≫ μ = 𝟙 coefficients.object := by
  let J := HomotopyGroup 0 ((HasFunctorialCofiber.cofib coefficientSelfUnit)⟦(-1 : ℤ)⟧)
  letI : HasCoproduct (fun _ : J => Sphere (C := Spectrum) 0) := smallSphereCoproduct J
  have hconn : IsConnected (∐ fun _ : J => Sphere (C := Spectrum) 0) (-1) :=
    smallSphereCoproduct_homotopy_vanishes J sphere_connected
  exact coefficientSelfUnit_retraction_of_sphere_coproduct hconn

end
end KIP126.Literature.Standard.HUnitCore
