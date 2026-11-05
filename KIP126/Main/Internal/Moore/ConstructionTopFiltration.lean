module

import KIP126.AdamsComputation.Moore.E2
import all KIP126.Main.Internal.Moore.ConstructionAnnihilation
import all KIP126.Main.Internal.Moore.ConstructionCrossing
import all KIP126.Main.Internal.NuThree.ClassicalZero

/-! The actual Moore top image has filtration at least nine.  This is the
zero composite of its bottom and top cell maps on E₂, transported through
the prescribed same-level quotient and suspension comparisons. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.Main.Internal KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem moore_top_of_bottom_source_zero :
    (background.classical.map KIP126.AdamsComputation.Moore.top).pageMap 2 (8,132)
      KIP126.AdamsComputation.Moore.bottomSource = 0 := by
  change ((background.classical.map KIP126.AdamsComputation.Moore.bottom).pageMap 2 (8,132) ≫
    (background.classical.map KIP126.AdamsComputation.Moore.top).pageMap 2 (8,132))
      (KIP126.Computation.Table.basis .sphere 8 132 0) = 0
  rw [←SpectralSequenceMorphism.pageMap_comp,←background.classical.map_comp,
    KIP126.AdamsComputation.Moore.bottom_top]
  exact KIP126.Main.Internal.NuThree.classical_page_zero (8,132) _

private theorem moore_suspension_reflects_filtration
    (X : SyntheticObject (coefficients := background.coefficients))
    (s m w k l : ℤ) (a : BiHom m w (X.obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower s
      (susp_invariance m w k l (X.obj background.nu background.auxiliary) a)) :
    FiltrationAtLeast background.syntheticTower s a := by
  let E := (essShift (k,l)).filtered X (m,w)
  have hsa : E.ambient.hom a =
      susp_invariance m w k l (X.obj background.nu background.auxiliary) a := by
    rw [(essShift (k,l)).ambient_eq X (m,w) a]
    change (SyntheticCategory.biShift_comp (m,w) (k,l)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (k,l)).map a =
      (SyntheticCategory.biShift_comp (m,w) (k,l)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (k,l)).map a ≫ 𝟙 _
    rw [Category.comp_id]
  have ham : susp_invariance m w k l (X.obj background.nu background.auxiliary) a ∈
      ModuleCat.subobjectModule _
        ((background.convergence (.shift (k,l) X)).filtration.F s ((m,w)+(k,l))) := by
    simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply,FiltrationAtLeast,Prod.mk_add_mk,SyntheticObject.obj] using ha
  obtain ⟨aa,haa⟩ := ham
  have hb : a ∈ ModuleCat.subobjectModule _
      ((background.convergence X).filtration.F s (m,w)) := by
    refine ⟨(E.level s).inv aa,?_⟩
    have h := ConcreteCategory.congr_hom (E.symm.level_arrow s) aa
    change _ = E.ambient.inv
      (((background.convergence (.shift (k,l) X)).filtration.F s ((m,w)+(k,l))).arrow aa) at h
    rw [haa,←hsa] at h
    exact h.trans (E.ambient.toLinearEquiv.symm_apply_apply a)
  simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
    OrderIso.apply_symm_apply,FiltrationAtLeast] using hb

/-- The literal quotient of ν(top) has zero leading E₂ label on the
specified bottom-cell source. -/
private theorem moore_raw_top_filtration_nine
    (c4 : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (hc4 : Detects (background.convergence
      (.quotient 4 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (8,132,132)
      (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 4 8 132 0
        KIP126.AdamsComputation.Moore.bottomSource) c4) :
    FiltrationAtLeast background.syntheticTower 9
      (c4 ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4) := by
  have hd := detects_map (.quotient 4 (.nu KIP126.AdamsComputation.Moore.adamsObject))
    (.quotient 4 (.nu (.shift 1 .sphere)))
    (XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4)
    (8,132,132) _ c4 hc4
  erw [moore_finite_label_natural KIP126.AdamsComputation.Moore.adamsObject
    (.shift 1 .sphere) KIP126.AdamsComputation.Moore.top 4 8 132 0
      KIP126.AdamsComputation.Moore.bottomSource,moore_top_of_bottom_source_zero] at hd
  have hz : finiteTargetLabel background (.shift 1 .sphere) 4 8 132 0 0 = 0 := by
    have cast_zero (A : SyntheticAdamsSS) (s t w w' : ℤ) (hw : w = w')
        (he : (A.E₂ (s,t,w) : Type) = (A.E₂ (s,t,w') : Type)) : he.mp 0 = 0 := by
      subst w'
      rfl
    simp only [finiteTargetLabel,targetNuLabel,map_zero]
    rw [cast_zero _ 8 132 (132+0-(0:ℕ)) (132-(0:ℕ)) (by decide)]
    simp only [map_zero]
  rw [hz] at hd
  exact detects_zero_filtration (background.convergence (.quotient 4 (.nu (.shift 1 .sphere))))
    (8,132,132) hd

/-- The desuspended Moore top image belongs to F⁹. -/
private theorem moore_top_image_filtration_nine
    (c4 : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (hc4 : Detects (background.convergence
      (.quotient 4 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (8,132,132)
      (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 4 8 132 0
        KIP126.AdamsComputation.Moore.bottomSource) c4) :
    FiltrationAtLeast background.syntheticTower 9 (mooreTopImage c4) := by
  have hr := moore_raw_top_filtration_nine c4 hc4
  have hs := map_preserves_filtration (background.convergentMap
    (.quotient 4 (.nu (.shift 1 .sphere))) (.shift (1,1) (.quotient 4 .sphere))
    (mooreNuSuspensionQuotientIso 4).hom) (124,132) 9 _ hr
  apply moore_suspension_reflects_filtration (.quotient 4 .sphere) 9 123 131 1 1
    (mooreTopImage c4)
  change FiltrationAtLeast background.syntheticTower 9
    (susp_invariance 123 131 1 1 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4)
      ((susp_invariance 123 131 1 1 _).symm _))
  rw [Equiv.apply_symm_apply]
  change FiltrationAtLeast background.syntheticTower 9
    ((c4 ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4) ≫
      (mooreNuSuspensionQuotientIso 4).hom) at hs
  simpa only [Category.assoc] using hs

end
end KIP126.Main.Internal.Moore
end
