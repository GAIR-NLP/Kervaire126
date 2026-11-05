module
import all KIP126.AdamsSynthetic.Internal.E2Cochain.E2Cohomology

namespace KIP126.AdamsSynthetic.Internal.E2Cochain
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v w
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000

private theorem ambientToZeroPage_natural
    {D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    (M : SSDataMorphism (ℤ × ℤ) D E) (p : ℤ × ℤ) (a : (D p).V) :
    ambientToZeroPage (E p) (M.φ p a) = M.pageMap p 0 (ambientToZeroPage (D p) a) := by
  have hm : M.φ p ≫ inv ((E p).Z 0).arrow =
      inv ((D p).Z 0).arrow ≫ M.cycleMap p 0 := by
    apply (cancel_epi ((D p).Z 0).arrow).mp
    simp only [IsIso.hom_inv_id_assoc]
    rw [← M.cycleMap_arrow_assoc]
    simp only [IsIso.hom_inv_id, Category.comp_id]
  change (M.φ p ≫ inv ((E p).Z 0).arrow ≫ (E p).pageπ 0) a =
    ((inv ((D p).Z 0).arrow ≫ (D p).pageπ 0) ≫ M.pageMap p 0) a
  rw [← Category.assoc, hm, Category.assoc, ← M.pageπ_pageMap]
  rfl

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X Y : C}
  {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y} {f : X ⟶ Y}
  {D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
  {dD : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}
  {dE : ∀ (r : ℤ) (p : ℤ × ℤ), (E p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (E (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}

private theorem cyclesToPage_natural
    (P : TowerSequencePresentation unit T D dD) (Q : TowerSequencePresentation unit U E dE)
    (φ : TowerMap unit T U f) (M : SSDataMorphism (ℤ × ℤ) D E)
    (hM : ∀ p (a : (D p).V), ((Q.ambient p).hom (M.φ p a)).val =
      ((P.ambient p).hom a).val ≫ φ.layer p.1)
    (p : ℤ × ℤ) (a : T.cycles 2 (by decide) p) :
    cyclesToPage Q p (Source.towerCycleMap φ p a) = M.pageMap p 0 (cyclesToPage P p a) := by
  obtain ⟨x,rfl⟩ := (ModuleCat.epi_iff_surjective (P.ambient p).hom).mp inferInstance a
  have heq : Source.towerCycleMap φ p ((P.ambient p).hom x) =
      (Q.ambient p).hom (M.φ p x) := Subtype.ext (hM p x).symm
  rw [heq, cyclesToPage_ambient, cyclesToPage_ambient]
  exact ambientToZeroPage_natural M p x

private theorem cochain_sc_kernel_eq (T : AbstractAdamsTower unit X) (t s : ℤ) :
    LinearMap.ker ((cochain T t).sc' (s-1) s (s+1)).g.hom = T.cycles 2 (by decide) (s,t) := by
  change LinearMap.ker ((cochain T t).d s (s+1)).hom = _
  rw [cochain_d]
  exact (cycles2_eq_ker T t s).symm

private theorem quotientIso_transport_mk
    {R : Type w} [Ring R] {A B C Z : ModuleCat.{v} R} (f : A ⟶ B) {g g' : B ⟶ C} (h : g = g')
    (e : ModuleCat.of R ((LinearMap.ker g'.hom) ⧸
      (LinearMap.range f.hom).comap (LinearMap.ker g'.hom).subtype) ≅ Z)
    (a : LinearMap.ker g.hom) :
    (Eq.mpr (congrArg (fun k : B ⟶ C => ModuleCat.of R ((LinearMap.ker k.hom) ⧸
      (LinearMap.range f.hom).comap (LinearMap.ker k.hom).subtype) ≅ Z) h) e).hom
      (Submodule.Quotient.mk a) =
    e.hom (Submodule.Quotient.mk (⟨a.val, by simpa only [← h] using a.property⟩ :
      LinearMap.ker g'.hom)) := by
  subst g'
  rfl

private theorem e2ShortComplexQuotientIso_mk
    (P : TowerSequencePresentation unit T D dD) (t s : ℤ)
    (a : LinearMap.ker ((cochain T t).sc' (s-1) s (s+1)).g.hom) :
    (e2ShortComplexQuotientIso P t s).hom (Submodule.Quotient.mk a) =
      cyclesToPage P (s,t) (LinearEquiv.ofEq _ _ (cochain_sc_kernel_eq T t s) a) := by
  change (Eq.mpr (congrArg (fun k : (cochain T t).X s ⟶ (cochain T t).X (s+1) =>
      ModuleCat.of ℤ ((LinearMap.ker k.hom) ⧸
        (LinearMap.range ((cochain T t).d (s-1) s).hom).comap
          (LinearMap.ker k.hom).subtype) ≅ (D (s,t)).page 0) (cochain_d T t s))
    (e2CochainQuotientEquiv P t s).toModuleIso).hom (Submodule.Quotient.mk a) = _
  refine (quotientIso_transport_mk ((cochain T t).d (s-1) s) (cochain_d T t s)
    (e2CochainQuotientEquiv P t s).toModuleIso a).trans ?_
  change e2CochainQuotientEquiv P t s (Submodule.Quotient.mk _) = _
  rw [e2CochainQuotientEquiv_mk]
  rfl

private def cochainCycleRepresentative (T : AbstractAdamsTower unit X) (t s : ℤ)
    (z : (cochain T t).cycles s) : T.cycles 2 (by decide) (s,t) :=
  LinearEquiv.ofEq _ _ (cochain_sc_kernel_eq T t s)
    (((cochain T t).sc' (s-1) s (s+1)).moduleCatCyclesIso.hom
      (((cochain T t).cyclesIsoSc' (s-1) s (s+1) (by simp) (by simp)).hom z))

private theorem cochainCycleRepresentative_val (T : AbstractAdamsTower unit X) (t s : ℤ)
    (z : (cochain T t).cycles s) :
    (cochainCycleRepresentative T t s z).val = (cochain T t).iCycles s z := by
  change (((cochain T t).cyclesIsoSc' (s-1) s (s+1) (by simp) (by simp)).hom ≫
    ((cochain T t).sc' (s-1) s (s+1)).moduleCatCyclesIso.hom ≫
    ((cochain T t).sc' (s-1) s (s+1)).moduleCatLeftHomologyData.i) z = _
  rw [ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  rfl

private theorem e2CohomologyIso_homologyπ
    (P : TowerSequencePresentation unit T D dD) (t s : ℤ)
    (z : (cochain T t).cycles s) :
    (e2CohomologyIso P t s).hom ((cochain T t).homologyπ s z) =
      cyclesToPage P (s,t) (cochainCycleRepresentative T t s z) := by
  have hh : (cochain T t).homologyπ s ≫ (e2CohomologyIso P t s).hom =
      ((cochain T t).cyclesIsoSc' (s-1) s (s+1) (by simp) (by simp)).hom ≫
      ((cochain T t).sc' (s-1) s (s+1)).moduleCatCyclesIso.hom ≫
      ((cochain T t).sc' (s-1) s (s+1)).moduleCatLeftHomologyData.π ≫
      (e2ShortComplexQuotientIso P t s).hom := by
    simp only [e2CohomologyIso, Iso.trans_hom]
    rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc,
      ShortComplex.π_moduleCatCyclesIso_hom_assoc]
  change ((cochain T t).homologyπ s ≫ (e2CohomologyIso P t s).hom) z = _
  rw [hh]
  exact e2ShortComplexQuotientIso_mk P t s _

private theorem cochainCycleRepresentative_natural (φ : TowerMap unit T U f) (t s : ℤ)
    (z : (cochain T t).cycles s) :
    cochainCycleRepresentative U t s (HomologicalComplex.cyclesMap (cochainMap φ t) s z) =
      Source.towerCycleMap φ (s,t) (cochainCycleRepresentative T t s z) := by
  apply Subtype.ext
  rw [cochainCycleRepresentative_val]
  change (HomologicalComplex.cyclesMap (cochainMap φ t) s ≫
    (cochain U t).iCycles s) z = _
  rw [HomologicalComplex.cyclesMap_i]
  change ((cochain T t).iCycles s z) ≫ φ.layer s =
    (cochainCycleRepresentative T t s z).val ≫ φ.layer s
  rw [cochainCycleRepresentative_val]

/-- Naturality of the fixed cohomology-to-E₂ isomorphisms for the original ambient square. -/
private theorem e2CohomologyIso_natural
    (P : TowerSequencePresentation unit T D dD) (Q : TowerSequencePresentation unit U E dE)
    (φ : TowerMap unit T U f) (M : SSDataMorphism (ℤ × ℤ) D E)
    (hM : ∀ p (a : (D p).V), ((Q.ambient p).hom (M.φ p a)).val =
      ((P.ambient p).hom a).val ≫ φ.layer p.1) (t s : ℤ) :
    HomologicalComplex.homologyMap (cochainMap φ t) s ≫ (e2CohomologyIso Q t s).hom =
      (e2CohomologyIso P t s).hom ≫ M.pageMap (s,t) 0 := by
  apply (cancel_epi ((cochain T t).homologyπ s)).mp
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (e2CohomologyIso Q t s).hom
      ((cochain U t).homologyπ s (HomologicalComplex.cyclesMap (cochainMap φ t) s z)) =
    M.pageMap (s,t) 0 ((e2CohomologyIso P t s).hom ((cochain T t).homologyπ s z))
  rw [e2CohomologyIso_homologyπ, e2CohomologyIso_homologyπ,
    cochainCycleRepresentative_natural]
  exact cyclesToPage_natural P Q φ M hM (s,t) _


end
end KIP126.AdamsSynthetic.Internal.E2Cochain
