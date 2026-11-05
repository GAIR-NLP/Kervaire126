module
import all KIP126.AdamsSynthetic.Completed.Acyclic

@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem homotopy_shift_injective {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ∀ n : ℤ, Function.Injective (inducedMap f n)) (n : ℤ) :
    Function.Injective (inducedMap ((shiftFunctor Spectrum (1 : ℤ)).map f) n) := by
  let E := shiftEquiv' Spectrum (-1 : ℤ) 1 (by omega)
  let adj := E.toAdjunction
  let e := (shiftFunctorAdd' Spectrum n (-1) (n-1) (by omega)).hom.app SphereSpectrum
  intro a b hab
  apply (adj.homEquiv (Sphere (C := Spectrum) n) X).symm.injective
  apply (cancel_epi e).mp
  apply (hf (n-1))
  change (e ≫ (adj.homEquiv _ X).symm a) ≫ f =
    (e ≫ (adj.homEquiv _ X).symm b) ≫ f
  rw [Category.assoc, Category.assoc,
    ← adj.homEquiv_naturality_right_symm a f,
    ← adj.homEquiv_naturality_right_symm b f]
  exact congrArg (fun z => e ≫ (adj.homEquiv _ Y).symm z) hab

/-- The actual completed stable homotopy groups detect isomorphisms of
    arbitrary fixed spectra. No completion or finite-type hypothesis occurs. -/
private theorem completed_isIso_of_homotopy_bijective {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ∀ n : ℤ, Function.Bijective (inducedMap f n)) : IsIso f := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang Spectrum := HasFunctorialCofiber.cofib_distinguished f
  apply (Triangle.isZero₃_iff_isIso₁ T hT).mp
  apply isZero_of_homotopy_zero
  intro n
  have hz (a : HomotopyGroup n T.obj₃) : a = 0 := by
    have hδ : a ≫ T.mor₃ = 0 := by
      apply homotopy_shift_injective f (fun k => (hf k).1) n
      change (a ≫ T.mor₃) ≫ (shiftFunctor Spectrum (1 : ℤ)).map T.mor₁ =
        0 ≫ (shiftFunctor Spectrum (1 : ℤ)).map T.mor₁
      rw [Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero, zero_comp]
    obtain ⟨b,hb⟩ := T.coyoneda_exact₃ hT a hδ
    obtain ⟨c,hc⟩ := (hf n).2 b
    change c ≫ T.mor₁ = b at hc
    rw [hb, ←hc, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end
end KIP126.AdamsSynthetic.Completed
end
