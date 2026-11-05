module

import all KIP126.AdamsSynthetic.Internal.E2Cochain.ElementaryFirstPage
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.AdamsNaturality
import Mathlib.Algebra.Homology.HomologicalComplex

namespace KIP126.AdamsSynthetic.Internal.E2Cochain
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X Y : C}

private def cochainDifferential (T : AbstractAdamsTower unit X) (t s : ℤ) :
    T.FirstPage (s,t) →ₗ[ℤ] T.FirstPage (s+1,t) :=
  towerFirstDifferential T (s,t)

private theorem cochainDifferential_sq (T : AbstractAdamsTower unit X) (t s : ℤ) :
    (cochainDifferential T t (s+1)).comp (cochainDifferential T t s) = 0 := by
  ext a
  dsimp only [cochainDifferential, towerFirstDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.zero_apply]
  rw [Source.connecting_layerMap T (s+1,t), map_zero, map_zero]

private def cochain (T : AbstractAdamsTower unit X) (t : ℤ) :
    CochainComplex (ModuleCat.{v} ℤ) ℤ :=
  CochainComplex.of (fun s => ModuleCat.of ℤ (T.FirstPage (s,t)))
    (fun s => ModuleCat.ofHom (cochainDifferential T t s)) (fun s => by
      ext a
      exact LinearMap.congr_fun (cochainDifferential_sq T t s) a)

private theorem cochain_d (T : AbstractAdamsTower unit X) (t s : ℤ) :
    (cochain T t).d s (s+1) = ModuleCat.ofHom (cochainDifferential T t s) :=
  by
    unfold cochain
    exact CochainComplex.of_d (fun s => ModuleCat.of ℤ (T.FirstPage (s,t)))
      (fun s => ModuleCat.ofHom (cochainDifferential T t s)) s

private theorem cycles2_eq_ker (T : AbstractAdamsTower unit X) (t s : ℤ) :
    T.cycles 2 (by omega) (s,t) = LinearMap.ker (cochainDifferential T t s) := by
  ext a
  exact (towerFirstDifferential_eq_zero_iff T (s,t) a).symm

private theorem boundaries2_succ_eq_range (T : AbstractAdamsTower unit X) (t s : ℤ) :
    T.boundaries 2 (by omega) (s+1,t) = LinearMap.range (cochainDifferential T t s) := by
  let hd : t-s-1 = t-(s+1) := by omega
  let e := homotopyDegreeEquiv (T.stageAt (s+1)) hd
  let e' := homotopyDegreeEquiv (T.stageAt s) hd
  have hs : (s+1) - 2 + 1 = s := by omega
  have recast (k : ℤ) (hk : k = s) (b : HomotopyGroup (t-(s+1)) (T.stageAt (s+1))) :
      (b ≫ T.mapAt (show k ≤ s+1 by omega) = 0) ↔
        (b ≫ T.mapAt (show s ≤ s+1 by omega) = 0) := by
    subst k
    rfl
  ext a
  constructor
  · rintro ⟨b, hb, hba⟩
    have hb' : b ≫ T.mapAt (show s ≤ s+1 by omega) = 0 := by
      apply (recast ((s+1)-2+1) hs b).mp
      exact hb
    have hb'' : e.symm b ≫ T.mapAt (show s ≤ s+1 by omega) = 0 := by
      apply e'.injective
      change homotopyDegreeEquiv _ hd (_ ≫ _) = _
      rw [homotopyDegreeEquiv_postcomp]
      change e (e.symm b) ≫ _ = _
      rw [LinearEquiv.apply_symm_apply, hb', map_zero]
    obtain ⟨z, hz⟩ := (Source.support_connecting_exact T (s,t) (e.symm b)).mp hb''
    refine ⟨z, ?_⟩
    change T.layerMap (s+1,t) (e (T.connecting (s,t) z)) = a
    rw [hz, LinearEquiv.apply_symm_apply]
    exact hba
  · rintro ⟨z, rfl⟩
    refine ⟨e (T.connecting (s,t) z), ?_, rfl⟩
    have hz := (Source.support_connecting_exact T (s,t) (T.connecting (s,t) z)).mpr ⟨z,rfl⟩
    have hb : e (T.connecting (s,t) z) ≫ T.mapAt (show s ≤ s+1 by omega) = 0 := by
      change homotopyDegreeEquiv _ hd _ ≫ _ = _
      rw [← homotopyDegreeEquiv_postcomp, hz, map_zero]
    exact (recast ((s+1)-2+1) hs _).mpr hb

private theorem boundaries2_eq_range (T : AbstractAdamsTower unit X) (t s : ℤ) :
    T.boundaries 2 (by omega) (s,t) = LinearMap.range ((cochain T t).d (s-1) s).hom := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, s = k+1 := ⟨s-1, by omega⟩
  change T.boundaries 2 _ (k+1,t) = LinearMap.range
    (CochainComplex.of.d (fun s => ModuleCat.of ℤ (T.FirstPage (s,t)))
      (fun s => ModuleCat.ofHom (cochainDifferential T t s)) (k+1-1) (k+1)).hom
  rw [add_sub_cancel_right, CochainComplex.of_d]
  exact boundaries2_succ_eq_range T t k

variable {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y} {f : X ⟶ Y}

private theorem cochainDifferential_natural (φ : TowerMap unit T U f) (t s : ℤ)
    (a : T.FirstPage (s,t)) :
    Source.towerE1Map φ (s+1,t) (cochainDifferential T t s a) =
      cochainDifferential U t s (Source.towerE1Map φ (s,t) a) := by
  dsimp only [cochainDifferential, towerFirstDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [Source.towerJ_natural, Source.towerK_natural]
  change U.layerMap (s+1,t) (homotopyDegreeEquiv _ _ _ ≫ φ.stage (s+1).toNat) =
    U.layerMap (s+1,t) (homotopyDegreeEquiv _ _ (_ ≫ φ.stage (s+1).toNat))
  rw [homotopyDegreeEquiv_postcomp]

/-- The chosen layer maps of one given tower map form a cochain map.
No functoriality of the chosen cofiber-map operation is assumed. -/
private def cochainMap (φ : TowerMap unit T U f) (t : ℤ) : cochain T t ⟶ cochain U t :=
  CochainComplex.ofHom (fun s => ModuleCat.ofHom (Source.towerE1Map φ (s,t))) (fun s => by
    rw [cochain_d, cochain_d]
    ext a
    exact (cochainDifferential_natural φ t s a).symm)


end
end KIP126.AdamsSynthetic.Internal.E2Cochain
