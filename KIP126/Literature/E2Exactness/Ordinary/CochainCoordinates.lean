module
import KIP126.AdamsSynthetic.E2Cochain

@[expose] section
namespace KIP126.Literature.Standard.CochainCoordinates
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.E2Cochain
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H X : C} {unit : SphereSpectrum ⟶ H}

private def homotopyDegreeEquiv (Y : C) {m n : ℤ} (h : m = n) :
    HomotopyGroup m Y ≃ₗ[ℤ] HomotopyGroup n Y := by
  subst n
  exact LinearEquiv.refl ℤ _

private theorem homotopyDegreeEquiv_postcomp {Y Z : C} {m n : ℤ} (h : m = n)
    (a : HomotopyGroup m Y) (f : Y ⟶ Z) :
    homotopyDegreeEquiv Z h (a ≫ f) = homotopyDegreeEquiv Y h a ≫ f := by
  subst n
  rfl

/-- The actual exact-couple first differential, including the ordinary
homotopy-degree identification at its target. -/
private noncomputable def towerFirstDifferential (T : AbstractAdamsTower unit X)
    (p : ℤ × ℤ) : T.FirstPage p →ₗ[ℤ] T.FirstPage (p.1+1,p.2) :=
  (T.layerMap (p.1+1,p.2)).comp
    ((homotopyDegreeEquiv (T.stageAt (p.1+1))
      (by dsimp; omega : p.2-p.1-1 = (p.1+1,p.2).2-(p.1+1,p.2).1)).toLinearMap.comp
        (T.connecting p))


private def cochainDifferential (T : AbstractAdamsTower unit X) (t s : ℤ) :
    T.FirstPage (s,t) →ₗ[ℤ] T.FirstPage (s+1,t) := towerFirstDifferential T (s,t)

private theorem degreeCast_eq {Y : C} {m n : ℤ} (h : m=n) (a : HomotopyGroup m Y) :
    homotopyDegreeEquiv Y h a = Eq.mp (congrArg (fun q => HomotopyGroup q Y) h) a := by
  subst n
  rfl

private theorem cochain_d (T : AbstractAdamsTower unit X) (t s : ℤ) :
    (cochain T t).d s (s+1) = ModuleCat.ofHom (cochainDifferential T t s) := by
  ext a
  rw [cochain_d_apply]
  change _ = homotopyDegreeEquiv _ _ (T.connecting (s,t) a) ≫ _
  rw [degreeCast_eq]

end
end KIP126.Literature.Standard.CochainCoordinates
end
