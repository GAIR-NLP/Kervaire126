module
public import KIP126.ProofTools.Operations
public import KIP126.Literature
import all KIP126.Main.Internal.Selected.LambdaOperations
/-! The canonical tower lift through the fixed filtered shift comparison.
Its graded map is the given convergence transport. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
private def weightShiftHom {m w : ℤ} {A : SyntheticSpectrum} (k : ℤ) (a : BiHom m w A) :
    BiHom m (w+k) ((SyntheticCategory.biShift (0,k)).obj A) :=
  (biShiftAddIso (m,w) (0,k) (m,w+k) (by ext <;> simp)).inv.app S_0_0 ≫
    (SyntheticCategory.biShift (0,k)).map a

private theorem shift_graded (X : SyntheticObject) (δ p : ℤ×ℤ) (s : ℤ)
    (S : SyntheticESSShiftComparison background δ)
    (e : ((background.family.obj (X.obj background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (aa : (Subobject.underlying.obj ((background.convergence X).filtration.F s p) : ModuleCat ℤ))
    (he : (towerGradedIso (background.convergence X) p s).hom e =
      (background.convergence X).filtration.toAssociatedGraded s p aa) :
    ∃ bb : (Subobject.underlying.obj ((background.convergence (.shift δ X)).filtration.F s (p+δ)) : ModuleCat ℤ),
      ((background.convergence (.shift δ X)).filtration.F s (p+δ)).arrow bb =
        shiftHomotopyClass δ p (((background.convergence X).filtration.F s p).arrow aa) ∧
      (towerGradedIso (background.convergence (.shift δ X)) (p+δ) s).hom
        ((towerInfinityIso (background.convergence X) (background.convergence (.shift δ X)) (S.filtered X p) s).hom e) =
      (background.convergence (.shift δ X)).filtration.toAssociatedGraded s (p+δ) bb := by
  let F := S.filtered X p
  refine ⟨(F.level s).hom aa,?_,?_⟩
  · exact (ConcreteCategory.congr_hom (F.level_arrow s) aa).trans (S.ambient_eq X p _)
  · change ((towerGradedIso (background.convergence X) p s).hom ≫ (F.gradedIso s).hom ≫
      (towerGradedIso (background.convergence (.shift δ X)) (p+δ) s).inv ≫
        (towerGradedIso (background.convergence (.shift δ X)) (p+δ) s).hom) e = _
    rw [Iso.inv_hom_id,Category.comp_id]
    change (F.gradedIso s).hom ((towerGradedIso (background.convergence X) p s).hom e)=_
    rw [he]
    exact ConcreteCategory.congr_hom (F.projection_comm s) aa

private theorem map_graded (X Y : SyntheticObject)
    (f : X.obj background.nu background.auxiliary ⟶ Y.obj background.nu background.auxiliary)
    (i : Tridegree)
    (e : ((background.family.obj (X.obj background.nu background.auxiliary)).sequence.ssData i).eInfty)
    (aa : (Subobject.underlying.obj ((background.convergence X).filtration.F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (he : ((background.convergence X).identification i).hom e =
      (background.convergence X).filtration.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) aa) :
    ∃ bb : (Subobject.underlying.obj ((background.convergence Y).filtration.F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ),
      ((background.convergence Y).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow bb =
        ((background.convergence X).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow aa ≫ f ∧
      ((background.convergence Y).identification i).hom ((background.family.map f).eInftyMap i e) =
      (background.convergence Y).filtration.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) bb := by
  let M := background.convergentMap X Y f
  let bb := (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose aa
  have hb : ((background.convergence Y).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow bb =
      ((background.convergence X).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow aa ≫ f := by
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose_spec aa
    change _ = M.filteredMap.map _ _ at h
    exact h.trans (ConcreteCategory.congr_hom (M.filteredMap_map _) _)
  refine ⟨bb,hb,?_⟩
  have hn := grade_natural X Y f i aa bb hb.symm
  have hx : ((background.convergence X).identification i).inv
      ((background.convergence X).filtration.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) aa)=e := by
    rw [←he]
    exact ((background.convergence X).identification i).toLinearEquiv.symm_apply_apply e
  rw [hx] at hn
  exact (congrArg ((background.convergence Y).identification i).hom hn).symm.trans
    (((background.convergence Y).identification i).toLinearEquiv.apply_symm_apply _)
end
end KIP126.Main.Internal.NuNinth
