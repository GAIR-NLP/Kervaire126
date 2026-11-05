module
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] section
namespace KIP126.Literature.Standard.ActualE2LES
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v
set_option autoImplicit false

private theorem range_eq_ker_of_iso
    {A B C A' B' C' : ModuleCat.{v} ℤ}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C')
    (hf : f ≫ eB.hom = eA.hom ≫ f') (hg : g ≫ eC.hom = eB.hom ≫ g')
    (h : LinearMap.range f.hom = LinearMap.ker g.hom) :
    LinearMap.range f'.hom = LinearMap.ker g'.hom := by
  have hf_apply (a : A) : eB.hom (f a) = f' (eA.hom a) :=
    congrArg (fun k : A ⟶ B' => k a) hf
  have hg_apply (b : B) : eC.hom (g b) = g' (eB.hom b) :=
    congrArg (fun k : B ⟶ C' => k b) hg
  ext b
  constructor
  · rintro ⟨a,rfl⟩
    let a₀ := eA.inv a
    have ha : eA.hom a₀ = a := by
      change (eA.inv ≫ eA.hom) a = a
      rw [eA.inv_hom_id]
      rfl
    have hz : g (f a₀) = 0 := by
      change f a₀ ∈ LinearMap.ker g.hom
      rw [← h]
      exact ⟨a₀,rfl⟩
    change g' (f' a) = 0
    rw [← ha, ← hf_apply, ← hg_apply, hz, map_zero]
  · intro hb
    let b₀ := eB.inv b
    have hb₀ : eB.hom b₀ = b := by
      change (eB.inv ≫ eB.hom) b = b
      rw [eB.inv_hom_id]
      rfl
    have hz : g b₀ = 0 := by
      apply (ConcreteCategory.isIso_iff_bijective eC.hom).mp inferInstance |>.injective
      rw [map_zero, hg_apply, hb₀]
      exact hb
    have hm : b₀ ∈ LinearMap.range f.hom := by rw [h]; exact hz
    obtain ⟨a,ha⟩ := hm
    refine ⟨eA.hom a, ?_⟩
    rw [← hf_apply, ha, hb₀]
end
end KIP126.Literature.Standard.ActualE2LES
end
