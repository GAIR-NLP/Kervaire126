module

public import KIP126.Main.Conditions
public import KIP126.ProofTools.Representatives

/-! Detection operations with common-representative transport. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem detects_infinity_equal (X : SyntheticObject) (i : Tridegree)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj background.nu background.auxiliary))
    (x y : (background.family.obj (X.obj background.nu background.auxiliary)).E₂ i)
    (ha : Detects (background.convergence X) i x a)
    (hb : Detects (background.convergence X) i y a) :
    ∃ e, HasInfinityRepresentative (background.family.obj (X.obj background.nu background.auxiliary)) 2 i x e ∧
      HasInfinityRepresentative (background.family.obj (X.obj background.nu background.auxiliary)) 2 i y e := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  have hab : a'=b' := (ModuleCat.mono_iff_injective _).mp inferInstance (ha'.trans hb'.symm)
  have hef : e=f := (ModuleCat.mono_iff_injective _).mp inferInstance (by rw [hga,hgb,hab])
  exact ⟨e,he,hef.symm ▸ hf⟩

theorem theta_detection_step
    (i : Tridegree) (x : background.family.sphere.E₂ i)
    (hframe : ∀ e : (background.family.sphere.sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative background.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast background.syntheticTower i.1 a) :
    DetectsNonzero (background.convergence .sphere) i x a ∨
      FiltrationAtLeast background.syntheticTower (i.1+1) a := by
  classical
  let F := background.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)
  have ham : a ∈ (ModuleCat.subobjectModule
      (syntheticHomotopy (S_0_0 : SyntheticSpectrum) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := ((background.convergence .sphere).identification i).inv q
  have he : ((background.convergence .sphere).identification i).hom e=q :=
    ConcreteCategory.congr_hom ((background.convergence .sphere).identification i).inv_hom_id q
  by_cases he0 : e=0
  · right
    have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
      rw [he0,map_zero] at he
      exact he.symm
    have hmem := (F.toAssociatedGraded_eq_zero_iff i.1 (i.2.1-i.1,i.2.2) a').mp hq
    rw [ha'] at hmem
    simpa only [F,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hmem
  · left
    have hr := (hframe e).resolve_left he0
    exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩

theorem survives_twelve_not_boundary_eleven (X : AdamsObject) (p : ℤ × ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 p)
    (hx : SurvivesTo (background.classical.obj (X.obj background.auxiliary)) 12 p x) :
    x ∉ KIP126.Literature.boundaries background X 11 p := by
  intro hxB
  obtain ⟨xr,hrep,hne⟩ := hx
  have hz : RepresentsOnPage (background.classical.obj (X.obj background.auxiliary)) 12 p x 0 :=
    KIP126.ProofTools.representsOnPage_of_congruent background X (by decide)
      (RepresentsOnPage.zero (by decide))
      ⟨by decide, by simpa only [sub_zero, Int.reduceSub] using hxB⟩
  exact hne (FinitePageCalculus.represents_unique hrep hz)

end
end KIP126.Main.Internal.Selected
