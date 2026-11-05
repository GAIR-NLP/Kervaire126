module
public import KIP126.AdamsSynthetic.Tower
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import all KIP126.AdamsSynthetic.Internal.E2Cochain.E2CohomologyNaturality

/-! The actual first differential, cochain complex and original tower-map action.
The fixed cohomology comparison keeps the original cycle/boundary quotient.
Generic representative and quotient constructions stay private in this module. -/
section
namespace KIP126.AdamsSynthetic.E2Cochain
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X Y : C}
  {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y} {f : X ⟶ Y}
  {D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
  {dD : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}
  {dE : ∀ (r : ℤ) (p : ℤ × ℤ), (E p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (E (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}


@[expose] public def firstDifferential (T : AbstractAdamsTower unit X) (t s : ℤ) :
    T.FirstPage (s,t) →ₗ[ℤ] T.FirstPage (s+1,t) :=
  (T.layerMap (s+1,t)).comp
    (((fun (Y : C) (m n : ℤ) (h : m=n) =>
      show HomotopyGroup m Y ≃ₗ[ℤ] HomotopyGroup n Y from by
        subst n
        exact LinearEquiv.refl ℤ _) (T.stageAt (s+1)) (t-s-1) (t-(s+1)) (by omega)).toLinearMap.comp
      (T.connecting (s,t)))

@[expose] public def cochain (T : AbstractAdamsTower unit X) (t : ℤ) :
    CochainComplex (ModuleCat.{v} ℤ) ℤ :=
  CochainComplex.of (fun s => ModuleCat.of ℤ (T.FirstPage (s,t)))
    (fun s => ModuleCat.ofHom (firstDifferential T t s)) (fun s => by
      ext a
      exact LinearMap.congr_fun (Internal.E2Cochain.cochainDifferential_sq T t s) a)

@[expose] public def cochainMap (φ : TowerMap unit T U f) (t : ℤ) : cochain T t ⟶ cochain U t :=
  CochainComplex.ofHom (fun s => ModuleCat.ofHom {
    toFun := fun a => a ≫ φ.layer s
    map_add' := by intros; simp only [Preadditive.add_comp]
    map_smul' := by intros; simp only [Preadditive.zsmul_comp, RingHom.id_apply] }) (fun s => by
      change (Internal.E2Cochain.cochainMap φ t).f s ≫
          (Internal.E2Cochain.cochain U t).d s (s+1) =
        (Internal.E2Cochain.cochain T t).d s (s+1) ≫ (Internal.E2Cochain.cochainMap φ t).f (s+1)
      exact (Internal.E2Cochain.cochainMap φ t).comm s (s+1))

omit [HasFunctorialCofiber (C := C)] in
private theorem degreeCast_eq {Y : C} {m n : ℤ} (h : m = n) (a : HomotopyGroup m Y) :
    Internal.E2Cochain.homotopyDegreeEquiv Y h a =
      Eq.mp (congrArg (fun q => HomotopyGroup q Y) h) a := by
  cases h
  rfl

public theorem cochain_d_apply (T : AbstractAdamsTower unit X) (t s : ℤ)
    (a : T.FirstPage (s,t)) :
    (cochain T t).d s (s+1) a =
      Eq.mp (congrArg (fun q => HomotopyGroup q (T.stageAt (s+1)))
        (by omega : t-s-1 = t-(s+1))) (T.connecting (s,t) a) ≫
        HasFunctorialCofiber.cofibι (T.mapAt (show s+1 ≤ (s+1)+1 by omega)) := by
  change (Internal.E2Cochain.cochain T t).d s (s+1) a = _
  rw [Internal.E2Cochain.cochain_d]
  change Internal.E2Cochain.homotopyDegreeEquiv _ _ (T.connecting (s,t) a) ≫ _ = _
  rw [degreeCast_eq]

public theorem cochainMap_f_apply (φ : TowerMap unit T U f) (t s : ℤ)
    (a : T.FirstPage (s,t)) : (cochainMap φ t).f s a = a ≫ φ.layer s := rfl

public def e2CohomologyIso (P : TowerSequencePresentation unit T D dD) (t s : ℤ) :
    (cochain T t).homology s ≅ (D (s,t)).page 0 := by
  exact Internal.E2Cochain.e2CohomologyIso P t s

public theorem e2CohomologyIso_natural
    (P : TowerSequencePresentation unit T D dD) (Q : TowerSequencePresentation unit U E dE)
    (φ : TowerMap unit T U f) (M : SSDataMorphism (ℤ × ℤ) D E)
    (hM : ∀ p (a : (D p).V), ((Q.ambient p).hom (M.φ p a)).val =
      ((P.ambient p).hom a).val ≫ φ.layer p.1) (t s : ℤ) :
    HomologicalComplex.homologyMap (cochainMap φ t) s ≫ (e2CohomologyIso Q t s).hom =
      (e2CohomologyIso P t s).hom ≫ M.pageMap (s,t) 0 :=
  Internal.E2Cochain.e2CohomologyIso_natural P Q φ M hM t s
end
end KIP126.AdamsSynthetic.E2Cochain
end
