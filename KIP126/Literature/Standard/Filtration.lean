module

public import KIP126.Literature.Standard
public import KIP126.Literature.Standard.QuotientAlgebra
import all KIP126.Literature.Standard.AdamsComparison
import all KIP126.Literature.Standard.FiniteLift
import all KIP126.Literature.Standard.RealizationLifts
import all KIP126.AdamsSynthetic.Completed.Background

/-! The selected-object action law in every degree of the homotopy filtration. -/



namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
universe u v

private theorem product_mem_top_cycles (D : SSData (ModuleCat.{v} ℤ)) (a : D.V)
    (ha : ∀ n : ℕ, a ∈ ModuleCat.subobjectModule _ (D.Z n)) :
    a ∈ ModuleCat.subobjectModule _ (D.Z ⊤) := by
  have hspan : (ModuleCat.subobjectModule _).symm (Submodule.span ℤ {a}) ≤ D.Z ⊤ := by
    apply D.Z_top_greatest
    intro n
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    simp only [OrderIso.apply_symm_apply, Submodule.span_le, Set.singleton_subset_iff]
    exact ha n
  have h := (ModuleCat.subobjectModule _).monotone hspan
  apply h
  rw [OrderIso.apply_symm_apply]
  exact Submodule.subset_span (by simp)

private theorem product_layerMap_mem_cycles {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1))
    (r : ℕ) (hr : 1 ≤ r) : T.layerMap p a ∈ T.cycles r hr p := by
  change T.connecting p (T.layerMap p a) ∈ LinearMap.range _
  have hz : T.connecting p (T.layerMap p a) = 0 := by
    change AbstractAdamsTower.desuspend _ _
      ((a ≫ HasFunctorialCofiber.cofibι _) ≫ HasFunctorialCofiber.cofibδ _) = 0
    have he : HasFunctorialCofiber.cofibι (T.mapAt (show p.1 ≤ p.1+1 by omega)) ≫
        HasFunctorialCofiber.cofibδ (T.mapAt (show p.1 ≤ p.1+1 by omega)) = 0 :=
      Pretriangulated.comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished _)
    rw [Category.assoc, he, comp_zero, map_zero]
  rw [hz]
  exact Submodule.zero_mem _

private theorem product_representative_of_lift {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} {T : AbstractAdamsTower unit X}
    {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    {d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (D (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ)}
    (P : TowerSequencePresentation unit T D d) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    ∃ z : (Subobject.underlying.obj ((D p).Z ⊤) : ModuleCat ℤ),
      P.infiniteRepresentativeE1 p z = T.layerMap p a := by
  let a₂ : T.cycles 2 (by decide) p := ⟨T.layerMap p a, product_layerMap_mem_cycles T p a 2 (by decide)⟩
  let x : (D p).V := (P.ambient p).inv a₂
  have hx : ∀ n : ℕ, x ∈ ModuleCat.subobjectModule _ ((D p).Z n) := by
    intro n
    apply (P.cycles p n x).mpr
    have he : (P.ambient p).hom x = a₂ := by simp only [x, Iso.inv_hom_id_apply]
    rw [he]
    exact product_layerMap_mem_cycles T p a (n+2) (by omega)
  obtain ⟨z, hz⟩ := product_mem_top_cycles (D p) x hx
  refine ⟨z, ?_⟩
  change ((P.ambient p).hom (((D p).Z ⊤).arrow z)).val = T.layerMap p a
  rw [hz]
  simp only [x, Iso.inv_hom_id_apply, a₂]

private theorem product_layerMap_natural {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X Y : C} {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
    {f : X ⟶ Y} (φ : TowerMap unit T U f) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    T.layerMap p a ≫ φ.layer p.1 = U.layerMap p (a ≫ φ.stage p.1.toNat) := by
  change (a ≫ HasFunctorialCofiber.cofibι _) ≫ φ.layer p.1 =
    (a ≫ φ.stage p.1.toNat) ≫ HasFunctorialCofiber.cofibι _
  rw [Category.assoc]
  change a ≫ HasFunctorialCofiber.cofibι _ ≫
    HasFunctorialCofiber.cofibMap _ _ _ _ _ = _
  rw [← HasFunctorialCofiber.cofibMap_ι, ← Category.assoc]

private theorem product_infinite_to_page_map
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (f : E ⟶ E') (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat ℤ)) :
    (Subobject.ofLE _ _ ((E'.ssData p).Z_anti le_top) ≫
      (E'.ssData p).pageπ (↑(2-E'.r₀).toNat : WithTop ℕ))
        (f.toSSDataMorphism.cycleMap p ⊤ z) =
    f.pageMap 2 p ((Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top) ≫
      (E.ssData p).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z) := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases E' with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  let n : WithTop ℕ := ↑(2-r₀).toNat
  have hs := f.toSSDataMorphism.cycleMap_ofLE_assoc p
      (r := n) (s := ⊤) le_top ((D' p).pageπ n)
  have hp := f.toSSDataMorphism.pageπ_pageMap p n
  have hq : (Subobject.ofLE ((D p).Z ⊤) ((D p).Z n) ((D p).Z_anti le_top) ≫
        (D p).pageπ n) ≫ f.toSSDataMorphism.pageMap p n =
        f.toSSDataMorphism.cycleMap p ⊤ ≫
          Subobject.ofLE ((D' p).Z ⊤) ((D' p).Z n) ((D' p).Z_anti le_top) ≫ (D' p).pageπ n := by
    rw [Category.assoc,hp]
    exact hs
  dsimp only [SpectralSequenceMorphism.pageMap, SpectralSequenceMorphism.toPreSSMorphism,
    PreSSMorphism.pageMap, SSDataMorphism.pageMapAt]
  simpa only [ModuleCat.comp_apply, eqToHom_refl, Category.comp_id, n]
    using (ConcreteCategory.congr_hom hq z).symm

private theorem product_classical_detects_map
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {H : C} {unit : SphereSpectrum ⟶ H} {A : ClassicalAdamsFamily C}
    (P : ClassicalTowerPresentation unit A) {X Y : C} (f : X ⟶ Y)
    (cx : ClassicalTowerConvergence P X) (cy : ClassicalTowerConvergence P Y)
    (p : ℤ × ℤ) (x : (A.obj X).Page 2 p) (a : HomotopyGroup (p.2-p.1) X)
    (hx : ClassicalDetects cx p x a) :
    ClassicalDetects cy p ((A.map f).pageMap 2 p x) (a ≫ f) := by
  obtain ⟨z, hz, b, hb, hg⟩ := hx
  let FX := (P.tower X).filtration
  let FY := (P.tower Y).filtration
  have hbmem : (FX.F p.1 (p.2-p.1)).arrow b ∈
      (P.tower X).filtrationSubmodule p.1 (p.2-p.1) := by
    have he : (FX.F p.1 (p.2-p.1)).arrow b ∈
        ModuleCat.subobjectModule _ (FX.F p.1 (p.2-p.1)) := ⟨b, rfl⟩
    simpa only [FX, AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using he
  obtain ⟨l, hl⟩ := hbmem
  change l ≫ (P.tower X).projection p.1 = (FX.F p.1 (p.2-p.1)).arrow b at hl
  obtain ⟨z₀, hz₀⟩ := product_representative_of_lift (P.sequence X) p l
  have hcx := cx.canonical p l z₀ hz₀ b hl.symm
  have he : ((A.obj X).ssData p).pageπ ⊤ z = ((A.obj X).ssData p).pageπ ⊤ z₀ := by
    apply (ModuleCat.mono_iff_injective (cx.identification p).hom).mp inferInstance
    exact hg.trans hcx.symm
  let zf := (A.map f).toSSDataMorphism.cycleMap p ⊤ z
  let zf₀ := (A.map f).toSSDataMorphism.cycleMap p ⊤ z₀
  have hzf (zz : (Subobject.underlying.obj (((A.obj X).ssData p).Z ⊤) : ModuleCat ℤ)) :
      (((A.obj Y).ssData p).Z ⊤).arrow ((A.map f).toSSDataMorphism.cycleMap p ⊤ zz) =
        (A.map f).φ p ((((A.obj X).ssData p).Z ⊤).arrow zz) :=
    ConcreteCategory.congr_hom ((A.map f).preserves_Z p ⊤).choose_spec zz
  let l' := l ≫ (P.map f).stage p.1.toNat
  have hzf₀ : (P.sequence Y).infiniteRepresentativeE1 p zf₀ = (P.tower Y).layerMap p l' := by
    change (((P.sequence Y).ambient p).hom
      ((((A.obj Y).ssData p).Z ⊤).arrow zf₀)).val = _
    rw [hzf, P.natural]
    change (P.sequence X).infiniteRepresentativeE1 p z₀ ≫ (P.map f).layer p.1 = _
    rw [hz₀, product_layerMap_natural]
  have hb'mem : a ≫ f ∈ ModuleCat.subobjectModule _ (FY.F p.1 (p.2-p.1)) := by
    change a ≫ f ∈ (ModuleCat.subobjectModule (AbstractAdamsTower.homotopy Y (p.2-p.1)))
      ((ModuleCat.subobjectModule (AbstractAdamsTower.homotopy Y (p.2-p.1))).symm ((P.tower Y).filtrationSubmodule p.1 (p.2-p.1)))
    rw [OrderIso.apply_symm_apply]
    refine ⟨l', ?_⟩
    change (l ≫ (P.map f).stage p.1.toNat) ≫ (P.tower Y).projection p.1 = a ≫ f
    rw [Category.assoc, (P.map f).projection, ← Category.assoc, hl, hb]
  obtain ⟨b', hb'⟩ := hb'mem
  have hbl : (FY.F p.1 (p.2-p.1)).arrow b' = l' ≫ (P.tower Y).projection p.1 := by
    rw [hb']
    dsimp only [l']
    rw [Category.assoc, (P.map f).projection, ← Category.assoc, hl, hb]
  have hcy := cy.canonical p l' zf₀ hzf₀ b' hbl
  have he' : ((A.obj Y).ssData p).pageπ ⊤ zf = ((A.obj Y).ssData p).pageπ ⊤ zf₀ := by
    have hm := congrArg ((A.map f).eInftyMap p) he
    have h₁ := ConcreteCategory.congr_hom ((A.map f).toSSDataMorphism.pageπ_pageMap p ⊤) z
    have h₂ := ConcreteCategory.congr_hom ((A.map f).toSSDataMorphism.pageπ_pageMap p ⊤) z₀
    exact h₁.symm.trans (hm.trans h₂)
  refine ⟨zf, ?_, b', hb', ?_⟩
  · simpa only [hz, zf] using product_infinite_to_page_map (A.map f) p z
  · rw [he']
    exact hcy

end
end KIP126.Literature.Standard

namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private def product_shift_conjugate (F : C ⥤ C) [F.CommShift ℤ]
    (j : F.obj (SphereSpectrum : C) ≅ SphereSpectrum) (n : ℤ)
    (a : HomotopyGroup (C := C) n SphereSpectrum) : HomotopyGroup (C := C) n SphereSpectrum :=
  (shiftFunctor C n).map j.inv ≫ (F.commShiftIso n).inv.app SphereSpectrum ≫ F.map a ≫ j.hom

private theorem product_shift_conjugate_mul (F : C ⥤ C) [F.CommShift ℤ]
    (j : F.obj (SphereSpectrum : C) ≅ SphereSpectrum) (m n : ℤ)
    (a : HomotopyGroup (C := C) m SphereSpectrum)
    (b : HomotopyGroup (C := C) n SphereSpectrum) :
    product_shift_conjugate F j (m+n)
      ((shiftFunctorAdd C m n).hom.app SphereSpectrum ≫ (shiftFunctor C n).map a ≫ b) =
    (shiftFunctorAdd C m n).hom.app SphereSpectrum ≫
      (shiftFunctor C n).map (product_shift_conjugate F j m a) ≫
        product_shift_conjugate F j n b := by
  simp only [product_shift_conjugate, Functor.map_comp, Category.assoc]
  rw [F.commShiftIso_add, Functor.CommShift.isoAdd_inv_app]
  simp only [Category.assoc]
  have h0 : F.map ((shiftFunctorAdd C m n).inv.app SphereSpectrum) ≫
      F.map ((shiftFunctorAdd C m n).hom.app SphereSpectrum) = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id_app, F.map_id]
  rw [← Category.assoc (F.map ((shiftFunctorAdd C m n).inv.app SphereSpectrum))
    (F.map ((shiftFunctorAdd C m n).hom.app SphereSpectrum)), h0, Category.id_comp]
  have hn := (F.commShiftIso n).inv.naturality_assoc a (F.map b ≫ j.hom)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  erw [(shiftFunctorAdd C m n).hom.naturality_assoc j.inv]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem product_unit_adjunction (B : ClosedSymmetricTensorTriangulated C)
    (n : ℤ) (f : HomotopyGroup n (mappingSpectrum B SphereSpectrum SphereSpectrum)) :
    letI := B.closed
    ((ihom.adjunction (SphereSpectrum : C)).homEquiv (Sphere n) SphereSpectrum).symm f =
      (λ_ (Sphere n : C)).hom ≫ f ≫ (sphereMappingIso B).hom := by
  letI := B.closed
  change (𝟙_ C ◁ f) ≫ (ihom.adjunction (𝟙_ C)).counit.app (𝟙_ C) = _
  have he : (sphereMappingIso B).hom =
      (λ_ ((ihom (𝟙_ C)).obj (𝟙_ C))).inv ≫
        (ihom.adjunction (𝟙_ C)).counit.app (𝟙_ C) := by
    change (conjugateEquiv (ihom.adjunction (𝟙_ C)) Adjunction.id
      (leftUnitorNatIso C).inv).app (𝟙_ C) = _
    exact conjugateEquiv_adjunction_id _ _ _
  rw [he]
  rw [← Category.assoc]
  erw [← leftUnitor_naturality f]
  dsimp only [mappingSpectrum, SphereSpectrum] at f ⊢
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem product_mapping_equiv_formula (B : ClosedSymmetricTensorTriangulated C)
    (n : ℤ) (f : HomotopyGroup n (mappingSpectrum B SphereSpectrum SphereSpectrum)) :
    letI := B.tensorShift (SphereSpectrum : C)
    mappingHomotopyEquiv B n SphereSpectrum SphereSpectrum f =
      product_shift_conjugate (tensorRight (SphereSpectrum : C)) (ρ_ (SphereSpectrum : C)) n
        (f ≫ (sphereMappingIso B).hom) := by
  letI := B.closed
  letI := B.symmetric
  letI := B.tensorShift (SphereSpectrum : C)
  dsimp only [mappingHomotopyEquiv, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk]
  erw [product_unit_adjunction B n f]
  simp only [Iso.refl_hom, Category.comp_id, Iso.trans_inv, Category.assoc]
  have hβ : (β_ (𝟙_ C) (Sphere n)).inv ≫ (λ_ (Sphere n : C)).hom =
      (ρ_ (Sphere n : C)).hom := by
    rw [← SymmetricCategory.braiding_swap_eq_inv_braiding (𝟙_ C) (Sphere n)]
    exact braiding_leftUnitor _
  rw [← Category.assoc (β_ (𝟙_ C) (Sphere n)).inv, hβ]
  dsimp only [product_shift_conjugate, ClosedSymmetricTensorTriangulated.sphereTensorShift]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  have hu : (λ_ (SphereSpectrum : C)).inv = (ρ_ (SphereSpectrum : C)).inv := by
    exact congrArg Iso.inv (Iso.ext (unitors_equal (C := C)))
  rw [hu]
  erw [← rightUnitor_naturality (f ≫ (sphereMappingIso B).hom)]
  rfl

private theorem product_mapping_composition (B : ClosedSymmetricTensorTriangulated C)
    (m n : ℤ)
    (a : HomotopyGroup m (mappingSpectrum B SphereSpectrum SphereSpectrum))
    (b : HomotopyGroup n (mappingSpectrum B SphereSpectrum SphereSpectrum)) :
    (mappingHomotopyEquiv B (m+n) SphereSpectrum SphereSpectrum).symm
      ((shiftFunctorAdd C m n).hom.app SphereSpectrum ≫
        (shiftFunctor C n).map (mappingHomotopyEquiv B m SphereSpectrum SphereSpectrum a) ≫
        mappingHomotopyEquiv B n SphereSpectrum SphereSpectrum b) ≫ (sphereMappingIso B).hom =
      (shiftFunctorAdd C m n).hom.app SphereSpectrum ≫
        (shiftFunctor C n).map (a ≫ (sphereMappingIso B).hom) ≫
          (b ≫ (sphereMappingIso B).hom) := by
  letI := B.tensorShift (SphereSpectrum : C)
  apply (cancel_mono (sphereMappingIso B).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (mappingHomotopyEquiv B (m+n) SphereSpectrum SphereSpectrum).injective
  rw [Equiv.apply_symm_apply, product_mapping_equiv_formula B (m+n)]
  simp only [Category.assoc]
  rw [product_shift_conjugate_mul, ← product_mapping_equiv_formula B m a,
    ← product_mapping_equiv_formula B n b]
end
end KIP126.Literature.Standard

namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem product_mapping_composition_regrade (m n r : ℤ) (h : r=m+n)
    (a : HomotopyGroup m (mappingSpectrum closedTensor SphereSpectrum SphereSpectrum))
    (b : HomotopyGroup n (mappingSpectrum closedTensor SphereSpectrum SphereSpectrum)) :
    (mappingHomotopyEquiv closedTensor r SphereSpectrum SphereSpectrum).symm
      (eqToHom (congrArg (Sphere (C := Spectrum)) h) ≫
        (shiftFunctorAdd Spectrum m n).hom.app SphereSpectrum ≫
        (shiftFunctor Spectrum n).map (mappingHomotopyEquiv closedTensor m SphereSpectrum SphereSpectrum a) ≫
        mappingHomotopyEquiv closedTensor n SphereSpectrum SphereSpectrum b) ≫ (sphereMappingIso closedTensor).hom =
      eqToHom (congrArg (Sphere (C := Spectrum)) h) ≫
        classicalSphereProduct (a ≫ (sphereMappingIso closedTensor).hom)
          (b ≫ (sphereMappingIso closedTensor).hom) := by
  subst r
  dsimp only [classicalSphereProduct, KIP126.Literature.classicalSphereProduct]
  simpa only [eqToHom_refl, Category.id_comp] using
    product_mapping_composition closedTensor m n a b

private theorem product_mapping_detects_iff
    (X Y : MappingObject (fun X : Spectrum => X = SphereSpectrum))
    (p : ℤ × ℤ) (x : (Moss.sequence mapping X Y).Page 2 p)
    (a : Moss.abutment (B := closedTensor) X Y (p.2-p.1)) :
    Moss.DetectsAbutment mapping X Y 2 p x a ↔
      ClassicalDetects (mapping.convergence X.val Y.val X.property Y.property) p x a := by
  constructor
  · rintro ⟨e, ⟨z, hz, he⟩, b, hb, hg⟩
    subst e
    exact ⟨z, hz, b, hb, hg⟩
  · rintro ⟨z, hz, b, hb, hg⟩
    exact ⟨_, ⟨z, hz, rfl⟩, b, hb, hg⟩

private theorem product_classical_detects_regrade
    {X : Spectrum} (c : ClassicalTowerConvergence background.classicalTower X)
    {p q : ℤ × ℤ} (h : p=q) (x : (background.classical.obj X).Page 2 p)
    (a : HomotopyGroup (p.2-p.1) X) (ha : ClassicalDetects c p x a) :
    ClassicalDetects c q
      (eqToHom (congrArg ((background.classical.obj X).Page 2) h) x)
      (eqToHom (congrArg (fun k : ℤ × ℤ => Sphere (C := Spectrum) (k.2-k.1)) h.symm) ≫ a) := by
  subst q
  simpa only [eqToHom_refl, ModuleCat.id_apply, Category.id_comp] using ha

end
end KIP126.Literature.Standard

namespace KIP126.Literature.Standard
open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed

public theorem action_filtration (X : SyntheticObject (coefficients := background.coefficients)) (m w m' w' s s' : ℤ)
    (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (b : BiHom m' w' (X.obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (hb : FiltrationAtLeast background.syntheticTower s' b) :
    FiltrationAtLeast background.syntheticTower (s+s') (sphereAction a b) := by
  sorry

/-- The general first-quotient multiplication comparison
composed with the specified sphere action. -/
public theorem first_quotient_action (s t s' t' : ℕ)
    (x : BiHom ((t : ℤ)-s) t (S_0_0 : SyntheticSpectrum))
    (y : BiHom ((t' : ℤ)-s') t' (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient background ((s+s' : ℕ) : ℤ) ((t+t' : ℕ) : ℤ)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]) (sphereAction x y)) =
      (eqToHom (congrArg (background.classical.sphere.Page 2)
        (show ((s : ℤ),(t : ℤ)) + ((s' : ℤ),(t' : ℤ)) = (((s+s' : ℕ) : ℤ),((t+t' : ℕ) : ℤ)) by
          simp only [Prod.mk_add_mk,Nat.cast_add])))
        (background.sphereAlgebra.product (s,t) (s',t')
          (KIP126.Literature.sphereFirstQuotient background s t (quotientClass 1 x))
          (KIP126.Literature.sphereFirstQuotient background s' t' y)) := by
  rw [← quotientAlgebra_sphere_action 1 (by decide) ((t : ℤ)-s) t ((t' : ℤ)-s') t' x y]
  exact quotientAlgebra_first_quotient s t s' t' (quotientClass 1 x) y


end KIP126.Literature.Standard




namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Synthetic.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn} {P : SyntheticTowerPresentation unit F} {X : Syn}

private theorem detects_zero_of_higher_filtration
    (c : SyntheticTowerConvergence P X) (i : Tridegree)
    (a : BiHom (i.2.1-i.1) i.2.2 X)
    (ha : FiltrationAtLeast P (i.1+1) a) : Detects c i 0 a := by
  let G := P.filtration X
  have haNext : a ∈ ModuleCat.subobjectModule _ (G.F (i.1+1) (i.2.1-i.1,i.2.2)) := by
    simpa only [G, SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
      FiltrationAtLeast] using ha
  have haThis : a ∈ ModuleCat.subobjectModule _ (G.F i.1 (i.2.1-i.1,i.2.2)) :=
    (ModuleCat.subobjectModule _).monotone (G.mono i.1 _) haNext
  obtain ⟨b, hb⟩ := haThis
  refine ⟨0, HasInfinityRepresentative.zero (F.obj X) 2 (by omega) i, b, hb, ?_⟩
  rw [map_zero]
  symm
  apply (G.toAssociatedGraded_eq_zero_iff i.1 (i.2.1-i.1,i.2.2) b).mpr
  rw [hb]
  exact haNext

private theorem detects_of_sub_filtration
    (c : SyntheticTowerConvergence P X) (i : Tridegree)
    {x : (F.obj X).E₂ i} {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a)
    (hb : FiltrationAtLeast P (i.1+1) (b-a)) : Detects c i x b := by
  have hzero := detects_zero_of_higher_filtration c i (b-a) hb
  have hadd := detects_add c i ha hzero
  have hab : a + (b-a) = b := by abel
  simpa only [add_zero, hab] using hadd

end
end KIP126.AdamsSynthetic



namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem sphereNu_page_comp {X Y Z : SyntheticSpectrum}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    background.family.pageMap (f≫g) r i =
      background.family.pageMap f r i ≫ background.family.pageMap g r i := by
  change (background.family.map (f≫g)).pageMap r i = _
  rw [SyntheticAdamsFamily.map_comp,SpectralSequenceMorphism.pageMap_comp]
  rfl

private theorem sphereNu_page_id (X : SyntheticSpectrum) (r : ℤ) (i : Tridegree) :
    background.family.pageMap (𝟙 X) r i = 𝟙 _ := by
  change (background.family.map (𝟙 X)).pageMap r i = _
  rw [SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.pageMap_id]

private theorem sphereNu_weight_label (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    nuWeightLabel background .sphere s t (t-k) (by omega) x =
      targetNuLabel background .sphere s t k x := by
  have hk : (t-(t-k)).toNat = k := by omega
  have cast_heq {A B : ModuleCat.{0} ℤ} (h : A=B) (a : A) : HEq ((eqToHom h) a) a := by
    subst B
    rfl
  have hlabel : HEq (targetNuLabel background .sphere s t (t-(t-k)).toNat x)
      (targetNuLabel background .sphere s t k x) := by
    congr 1
  unfold nuWeightLabel regradeE2
  exact eq_of_heq ((cast_heq _ _).trans hlabel)

private theorem sphereNu_forward_label (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    background.family.pageMap background.nu.unitIso.hom 2 (s,t,t-k)
      (nuWeightLabel background .sphere s t (t-k) (by omega) x) =
      background.comparison.sphereE2 s t k x := by
  rw [sphereNu_weight_label]
  have h := background.comparison.sphere_nu s t k x
  change background.family.pageMap
    (SyntheticCategory.biShift_zero.hom.app _ ≫ background.nu.unitIso.hom) 2 (s,t,t-k)
    _ = _ at h
  rw [sphereNu_page_comp] at h
  exact h

private theorem sphereNu_inverse_label (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    background.family.pageMap background.nu.unitIso.inv 2 (s,t,t-k)
      (background.comparison.sphereE2 s t k x) =
      nuWeightLabel background .sphere s t (t-k) (by omega) x := by
  rw [←sphereNu_forward_label]
  change (background.family.pageMap background.nu.unitIso.hom 2 (s,t,t-k) ≫
    background.family.pageMap background.nu.unitIso.inv 2 (s,t,t-k)) _ = _
  rw [←sphereNu_page_comp,Iso.hom_inv_id,sphereNu_page_id,ModuleCat.id_apply]

private theorem sphereNu_detects_forward (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (S_0_0:SyntheticSpectrum))
    (ha : Detects (background.convergence .sphere) (s,t,t-k)
      (background.comparison.sphereE2 s t k x) a) :
    Detects (background.convergence (.nu .sphere)) (s,t,t-k)
      (nuWeightLabel background .sphere s t (t-k) (by omega) x)
      (a≫background.nu.unitIso.inv) := by
  have h := SelectedLifetimeConstruction.detects_map .sphere (.nu .sphere)
    background.nu.unitIso.inv (s,t,t-k) _ _ ha
  change Detects (background.convergence (.nu .sphere)) (s,t,t-k)
    (background.family.pageMap background.nu.unitIso.inv 2 (s,t,t-k)
      (background.comparison.sphereE2 s t k x)) (a≫background.nu.unitIso.inv) at h
  rw [sphereNu_inverse_label] at h
  exact h

private theorem sphereNu_detects_reverse (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (background.nu.functor.obj SphereSpectrum))
    (ha : Detects (background.convergence (.nu .sphere)) (s,t,t-k)
      (nuWeightLabel background .sphere s t (t-k) (by omega) x) a) :
    Detects (background.convergence .sphere) (s,t,t-k)
      (background.comparison.sphereE2 s t k x) (a≫background.nu.unitIso.hom) := by
  have h := SelectedLifetimeConstruction.detects_map (.nu .sphere) .sphere
    background.nu.unitIso.hom (s,t,t-k) _ _ ha
  change Detects (background.convergence .sphere) (s,t,t-k)
    (background.family.pageMap background.nu.unitIso.hom 2 (s,t,t-k)
      (nuWeightLabel background .sphere s t (t-k) (by omega) x))
      (a≫background.nu.unitIso.hom) at h
  rw [sphereNu_forward_label] at h
  exact h

private def sphereNu_quotientIso (q : ℕ) :
    XModLambdaN (S_0_0:SyntheticSpectrum) q ≅
      XModLambdaN (background.nu.functor.obj SphereSpectrum) q :=
  (background.quotients.functoriality.functor q).mapIso background.nu.unitIso.symm

private theorem sphereNu_finite_forward_label (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    background.family.pageMap (XModLambdaN.map background.nu.unitIso.inv q) 2 (s,t,t-k)
      ((background.family.quotientProjection (S_0_0:SyntheticSpectrum) q).pageMap 2 (s,t,t-k)
        (background.comparison.sphereE2 s t k x)) =
    (background.family.quotientProjection (background.nu.functor.obj SphereSpectrum) q).pageMap 2 (s,t,t-k)
      (nuWeightLabel background .sphere s t (t-k) (by omega) x) := by
  change (background.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,t-k) ≫
      background.family.pageMap (XModLambdaN.map background.nu.unitIso.inv q) 2 (s,t,t-k)) _ = _
  rw [←sphereNu_page_comp,←XModLambdaN.incl_naturality,sphereNu_page_comp]
  change background.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,t-k)
    (background.family.pageMap background.nu.unitIso.inv 2 (s,t,t-k) _) = _
  rw [sphereNu_inverse_label]
  rfl

private theorem sphereNu_finite_reverse_label (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    background.family.pageMap (XModLambdaN.map background.nu.unitIso.hom q) 2 (s,t,t-k)
      ((background.family.quotientProjection (background.nu.functor.obj SphereSpectrum) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel background .sphere s t (t-k) (by omega) x)) =
    (background.family.quotientProjection (S_0_0:SyntheticSpectrum) q).pageMap 2 (s,t,t-k)
      (background.comparison.sphereE2 s t k x) := by
  change (background.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,t-k) ≫
      background.family.pageMap (XModLambdaN.map background.nu.unitIso.hom q) 2 (s,t,t-k)) _ = _
  rw [←sphereNu_page_comp,←XModLambdaN.incl_naturality,sphereNu_page_comp]
  change background.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,t-k)
    (background.family.pageMap background.nu.unitIso.hom 2 (s,t,t-k) _) = _
  rw [sphereNu_forward_label]
  rfl

private theorem sphereNu_finite_detects_forward (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0:SyntheticSpectrum) q))
    (ha : Detects (background.convergence (.quotient q .sphere)) (s,t,t-k)
      ((background.family.quotientProjection (S_0_0:SyntheticSpectrum) q).pageMap 2 (s,t,t-k)
        (background.comparison.sphereE2 s t k x)) a) :
    Detects (background.convergence (.quotient q (.nu .sphere))) (s,t,t-k)
      ((background.family.quotientProjection (background.nu.functor.obj SphereSpectrum) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel background .sphere s t (t-k) (by omega) x))
      (a≫XModLambdaN.map background.nu.unitIso.inv q) := by
  have h := SelectedLifetimeConstruction.detects_map (.quotient q .sphere)
    (.quotient q (.nu .sphere)) (XModLambdaN.map background.nu.unitIso.inv q)
      (s,t,t-k) _ _ ha
  change Detects (background.convergence (.quotient q (.nu .sphere))) (s,t,t-k)
    (background.family.pageMap (XModLambdaN.map background.nu.unitIso.inv q) 2 (s,t,t-k)
      ((background.family.quotientProjection (S_0_0:SyntheticSpectrum) q).pageMap 2 (s,t,t-k)
        (background.comparison.sphereE2 s t k x)))
      (a≫XModLambdaN.map background.nu.unitIso.inv q) at h
  rw [sphereNu_finite_forward_label] at h
  exact h

private theorem sphereNu_finite_detects_reverse (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : Detects (background.convergence (.quotient q (.nu .sphere))) (s,t,t-k)
      ((background.family.quotientProjection (background.nu.functor.obj SphereSpectrum) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel background .sphere s t (t-k) (by omega) x)) a) :
    Detects (background.convergence (.quotient q .sphere)) (s,t,t-k)
      ((background.family.quotientProjection (S_0_0:SyntheticSpectrum) q).pageMap 2 (s,t,t-k)
        (background.comparison.sphereE2 s t k x))
      (a≫XModLambdaN.map background.nu.unitIso.hom q) := by
  have h := SelectedLifetimeConstruction.detects_map (.quotient q (.nu .sphere))
    (.quotient q .sphere) (XModLambdaN.map background.nu.unitIso.hom q)
      (s,t,t-k) _ _ ha
  change Detects (background.convergence (.quotient q .sphere)) (s,t,t-k)
    (background.family.pageMap (XModLambdaN.map background.nu.unitIso.hom q) 2 (s,t,t-k)
      ((background.family.quotientProjection (background.nu.functor.obj SphereSpectrum) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel background .sphere s t (t-k) (by omega) x)))
      (a≫XModLambdaN.map background.nu.unitIso.hom q) at h
  rw [sphereNu_finite_reverse_label] at h
  exact h

private theorem sphereNu_diagonal_first_projection (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) t (background.nu.functor.obj SphereSpectrum))
    (ha : Detects (background.convergence (.nu .sphere)) (s,t,t)
      (nuWeightLabel background .sphere s t t (by omega) x) a) :
    quotientClass 1 (a≫background.nu.unitIso.hom) =
      nativeLabel .sphere s t x ≫ XModLambdaN.map background.nu.unitIso.hom 1 := by
  have hp := SelectedLifetimeConstruction.projection_eq_first_of_detects
    .sphere s t x a ha
  change a ≫ XModLambdaN.incl (background.nu.functor.obj SphereSpectrum) 1 =
    nativeLabel .sphere s t x at hp
  dsimp only [quotientClass]
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
  exact congrArg (fun z => z ≫ XModLambdaN.map background.nu.unitIso.hom 1) hp

end
end KIP126.Literature.Standard


namespace AssemblyLambda

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem regrade_eq_comp {X : Syn} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a : BiHom m w X) :
    homotopyRegrade hm hw a = eqToHom (by subst m'; subst w'; rfl) ≫ a := by
  subst m'; subst w'; simp only [homotopyRegrade,eqToHom_refl,Category.id_comp]

private theorem action_lambda_general (coh : BiShiftCoherence Syn)
    (k : ℕ) (m w n z : ℤ) {X : Syn}
    (a : BiHom m w (S_0_0 : Syn)) (b : BiHom n z X) :
    sphereAction (lambdaMultiply k a) b =
      homotopyRegrade rfl (by omega : (w+z)-(k:ℤ) = (w-(k:ℤ))+z)
        (lambdaMultiply k (sphereAction a b)) := by
  let shiftSwap (a b : ℤ × ℤ) (A : Syn) :
      (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
    (biShiftAddIso a b (a+b) rfl).app A ≪≫
      ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm
  have shiftSwap_add (coh : BiShiftCoherence Syn)
      (a b c : ℤ × ℤ) (A : Syn) :
      (shiftSwap a (b+c) A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c (b+c) rfl).inv.app A) =
      (biShiftAddIso b c (b+c) rfl).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    let habc : (a+b)+c=a+(b+c) := add_assoc a b c
    let hbac : b+(a+c)=a+(b+c) := by abel
    have h₁ := coh.associativity a b c (a+b) (b+c) (a+(b+c)) rfl rfl habc rfl A
    have h₂ := coh.associativity b a c (a+b) (a+c) (a+(b+c))
      (add_comm _ _) rfl habc hbac A
    have h₃ := coh.associativity b c a (b+c) (a+c) (a+(b+c))
      rfl (add_comm _ _) (add_comm _ _) hbac A
    simp (config := { congrConsts := false }) only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
    rw [Functor.map_comp]
    apply (cancel_epi ((biShiftAddIso b c (b+c) rfl).hom.app
      ((SyntheticCategory.biShift a).obj A))).mp
    simp (config := { congrConsts := false }) only [Category.assoc,Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc,← h₁]
    simp (config := { congrConsts := false }) only [Category.assoc]
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso a b (a+b) rfl).hom.app A))).mpr
    -- Cancel the common left factor introduced by the first associativity square.
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso b a (a+b) (add_comm _ _)).hom.app A))).mp
    simp (config := { congrConsts := false }) only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
    rw [← Category.assoc,h₂]
    simp (config := { congrConsts := false }) only [Category.assoc]
    apply (cancel_epi ((biShiftAddIso a c (a+c) rfl).hom.app
      ((SyntheticCategory.biShift b).obj A))).mpr
    apply (cancel_epi ((biShiftAddIso c a (a+c) (add_comm _ _)).hom.app
      ((SyntheticCategory.biShift b).obj A))).mp
    rw [← Category.assoc,← Category.assoc,← h₃]
    simp (config := { congrConsts := false }) only [Category.assoc,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Category.id_comp,←Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]
    rfl
  have shiftSwap_add_eq (coh : BiShiftCoherence Syn)
      (a b c d : ℤ × ℤ) (h : b+c=d) (A : Syn) :
      (shiftSwap a d A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
      (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    subst d
    exact shiftSwap_add coh a b c A
  have shiftSwap_natural (a b : ℤ × ℤ) {A B : Syn} (f : A ⟶ B) :
      (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
        (shiftSwap a b B).hom =
      (shiftSwap a b A).hom ≫
        (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
    exact ((biShiftAddIso a b (a+b) rfl) ≪≫
      (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f
  have shiftSwap_hom_eq (a b d : ℤ × ℤ)
      (hab : a+b=d) (hba : b+a=d) (A : Syn) :
      (shiftSwap a b A).hom =
        (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
    subst d
    rfl
  have lambda_pow_shift (coh : BiShiftCoherence Syn)
      (n : ℕ) (a : ℤ × ℤ) (A : Syn) :
      lambdaPow n ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) A).hom ≫
          (SyntheticCategory.biShift a).map (lambdaPow n A) := by
    induction n generalizing A with
    | zero =>
      change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a 0 A).hom ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A)
      have h : SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
          (biShiftAddIso a 0 a (add_zero a)).hom.app A ≫
            (biShiftAddIso 0 a a (zero_add a)).inv.app A ≫
              (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A) := by
        rw [←coh.left_unit a A,Iso.inv_hom_id_app,Category.comp_id]
        exact (coh.right_unit a A).symm
      rw [shiftSwap_hom_eq a 0 a (add_zero a) (zero_add a),Category.assoc]
      exact h
    | succ n ih =>
      have h1 : lambdaPow 1 ((SyntheticCategory.biShift a).obj A) =
          (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
            (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
        rw [lambdaPow_one coh,lambdaPow_one coh]
        change SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj A) =
          (shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app A)
        rw [shiftSwap_hom_eq a (0,-1) (a+(0,-1)) rfl (add_comm _ _),Category.assoc]
        exact coh.lambda_comm a A
      have hn := shiftSwap_natural a (KIP126.Synthetic.Context.lambdaDegree n) (lambdaPow 1 A)
      have hh := shiftSwap_add_eq coh a (KIP126.Synthetic.Context.lambdaDegree 1) (KIP126.Synthetic.Context.lambdaDegree n)
        (KIP126.Synthetic.Context.lambdaDegree (n+1)) (by ext <;> simp [KIP126.Synthetic.Context.lambdaDegree]) A
      change (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree (n+1)) A).hom ≫
          (SyntheticCategory.biShift a).map ((lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app A) =
        (lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app ((SyntheticCategory.biShift a).obj A) ≫
          (SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree n)).map (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
          (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree 1)).obj A)).hom at hh
      rw [lambdaPow_add coh 1 n (n+1) (by omega) ((SyntheticCategory.biShift a).obj A),
        lambdaPow_add coh 1 n (n+1) (by omega) A,h1,ih]
      simp (config := { congrConsts := false }) only [Functor.map_comp,Category.assoc]
      rw [reassoc_of% hn]
      rw [reassoc_of% hh]
      rfl
  have shift_assoc_inv (coh : BiShiftCoherence Syn)
      (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
      (habc : ab+c=total) (habc' : a+bc=total) (A : Syn) :
      (biShiftAddIso ab c total habc).inv.app A ≫
        (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
      (biShiftAddIso a bc total habc').inv.app A ≫
        (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
    have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
        (biShiftAddIso ab c total habc).app A) =
      ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
        (biShiftAddIso a bc total habc').app A) :=
      Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
    have hi := congrArg Iso.inv he
    exact hi
  let S := (S_0_0 : Syn)
  have h₁ := shift_assoc_inv coh (m,w) (n,z) (0,-(k:ℤ))
    (m+n,w+z) (n,z-(k:ℤ)) (m+n,(w+z)-(k:ℤ))
    (by rfl) (by ext <;> simp [sub_eq_add_neg])
    (by ext <;> simp [sub_eq_add_neg]) (by ext <;> simp [sub_eq_add_neg,add_assoc]) S
  have h₂ := shift_assoc_inv coh (m,w) (0,-(k:ℤ)) (n,z)
    (m,w-(k:ℤ)) (n,z-(k:ℤ)) (m+n,(w+z)-(k:ℤ))
    (by ext <;> simp [sub_eq_add_neg]) (by ext <;> simp [sub_eq_add_neg,add_comm])
    (by ext <;> simp [sub_eq_add_neg]; abel) (by ext <;> simp [sub_eq_add_neg,add_assoc]) S
  have hp :
      (biShiftAddIso (m+n,w+z) (0,-(k:ℤ)) (m+n,(w+z)-(k:ℤ)) (by ext <;> simp [sub_eq_add_neg])).inv.app S ≫
        lambdaPow k (Smn (m+n) (w+z)) ≫
        (SyntheticCategory.biShift_comp (m,w) (n,z)).inv.app S =
      (biShiftAddIso (m,w-(k:ℤ)) (n,z) (m+n,(w+z)-(k:ℤ)) (by ext <;> simp [sub_eq_add_neg]; abel)).inv.app S ≫
        (SyntheticCategory.biShift (n,z)).map
          ((biShiftAddIso (m,w) (0,-(k:ℤ)) (m,w-(k:ℤ)) (by ext <;> simp [sub_eq_add_neg])).inv.app S) ≫
        (SyntheticCategory.biShift (n,z)).map (lambdaPow k (Smn m w)) := by
    rw [←lambdaPow_naturality]
    change (biShiftAddIso (m+n,w+z) (0,-(k:ℤ)) (m+n,(w+z)-(k:ℤ)) _).inv.app S ≫
      (SyntheticCategory.biShift (0,-(k:ℤ))).map ((SyntheticCategory.biShift_comp (m,w) (n,z)).inv.app S) ≫
      lambdaPow k ((SyntheticCategory.biShift (n,z)).obj (Smn m w)) = _
    rw [lambda_pow_shift coh k (n,z) (Smn m w)]
    dsimp only [lambdaDegree]
    rw [shiftSwap_hom_eq (n,z) (0,-(k:ℤ)) (n,z-(k:ℤ))
      (by ext <;> simp [sub_eq_add_neg]) (by ext <;> simp [sub_eq_add_neg,add_comm])]
    have hpq : (biShiftAddIso (m,w) (n,z) (m+n,w+z) rfl).inv.app S =
        (SyntheticCategory.biShift_comp (m,w) (n,z)).inv.app S := by
      simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp]
    rw [← hpq]
    simp (config := { congrConsts := false }) only [Category.assoc]
    rw [← Category.assoc, h₁]
    simp (config := { congrConsts := false }) only [Category.assoc,Smn,S,Iso.inv_hom_id_app_assoc]
    simpa (config := { congrConsts := false }) only [Category.assoc,Smn,S] using
      (congrArg (fun f => f ≫ (SyntheticCategory.biShift (n,z)).map (lambdaPow k (Smn m w))) h₂.symm)
  have h := congrArg (fun f => f ≫ (SyntheticCategory.biShift (n,z)).map a ≫ b) hp
  apply (cancel_epi (eqToHom (congrArg (fun j => Smn (m+n) j (Syn := Syn))
    (show (w+z)-(k:ℤ)=(w-(k:ℤ))+z by omega)))).mp
  rw [regrade_eq_comp]
  simp only [← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]
  delta sphereAction lambdaMultiply
  simp (config := { congrConsts := false }) only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    NatTrans.comp_app,eqToHom_app,eqToHom_map,Functor.map_comp,Category.assoc] at h ⊢
  exact h.symm


end
end AssemblyLambda


namespace AssemblyShift

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn] [HasFunctorialCofiber (C := Syn)]
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

omit [HasFunctorialCofiber (C := Syn)] in
private theorem regrade_eq_comp {X : Syn} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a : BiHom m w X) :
    homotopyRegrade hm hw a = eqToHom (by subst m'; subst w'; rfl) ≫ a := by
  subst m'; subst w'; simp only [homotopyRegrade,eqToHom_refl,Category.id_comp]

omit [HasFunctorialCofiber (C := Syn)] in
private theorem action_shift_general (coh : BiShiftCoherence Syn)
    (δ : ℤ × ℤ) (m w n z : ℤ) {X : Syn}
    (a : BiHom m w (S_0_0 : Syn)) (b : BiHom n z X) :
    sphereAction a (shiftHomotopyClass δ (n,z) b) =
      homotopyRegrade (add_assoc m n δ.1) (add_assoc w z δ.2)
        (shiftHomotopyClass δ (m+n,w+z) (sphereAction a b)) := by
  have h := coh.associativity (m,w) (n,z) δ (m+n,w+z) ((n,z)+δ)
    ((m,w)+((n,z)+δ)) rfl rfl (add_assoc (m,w) (n,z) δ) rfl (S_0_0 : Syn)
  have he : ((SyntheticCategory.biShift δ).mapIso
      ((biShiftAddIso (m,w) (n,z) (m+n,w+z) rfl).app (S_0_0 : Syn)) ≪≫
      (biShiftAddIso (m+n,w+z) δ ((m,w)+((n,z)+δ)) (add_assoc (m,w) (n,z) δ)).app S_0_0) =
    ((biShiftAddIso (n,z) δ ((n,z)+δ) rfl).app ((SyntheticCategory.biShift (m,w)).obj S_0_0) ≪≫
      (biShiftAddIso (m,w) ((n,z)+δ) ((m,w)+((n,z)+δ)) rfl).app S_0_0) := Iso.ext h
  have hi := congrArg Iso.inv he
  have hn := ((SyntheticCategory.biShift_comp (n,z) δ).inv.naturality a)
  delta sphereAction shiftHomotopyClass
  rw [regrade_eq_comp]
  simp only [Functor.map_comp]
  rw [reassoc_of% hn]
  simp (config := { congrConsts := false }) only [Iso.app_inv,biShiftAddIso,Iso.trans_inv,
    eqToIso.inv,NatTrans.comp_app,eqToHom_app,eqToHom_refl,
    Category.id_comp,Functor.mapIso_inv] at hi
  have hh := congrArg (fun f => f ≫ (SyntheticCategory.biShift δ).map
    ((SyntheticCategory.biShift (n,z)).map a) ≫ (SyntheticCategory.biShift δ).map b) hi
  simpa (config := { congrConsts := false }) only [Category.assoc,Smn] using hh.symm

omit [HasFunctorialCofiber (C := Syn)] in
private theorem action_shift_postmap_general (coh : BiShiftCoherence Syn)
    (δ : ℤ × ℤ) (m w n z : ℤ) {X Y : Syn}
    (a : BiHom m w (S_0_0 : Syn)) (b : BiHom n z X)
    (L : (SyntheticCategory.biShift δ).obj X ⟶ Y) :
    sphereAction a (shiftHomotopyClass δ (n,z) b ≫ L) =
      homotopyRegrade (add_assoc m n δ.1) (add_assoc w z δ.2)
        (shiftHomotopyClass δ (m+n,w+z) (sphereAction a b)) ≫ L := by
  simpa only [sphereAction,Category.assoc] using
    congrArg (fun f => f ≫ L) (action_shift_general coh δ m w n z a b)

omit [HasFunctorialCofiber (C := Syn)] in
private theorem lambdaMultiply_zero_general (coh : BiShiftCoherence Syn)
    (m w : ℤ) {X : Syn} (a : BiHom m w X) :
    homotopyRegrade rfl (sub_zero w) (lambdaMultiply 0 a) = a := by
  have hu := coh.right_unit (m,w) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,NatTrans.comp_app,eqToHom_app] at hu
  rw [regrade_eq_comp]
  delta lambdaMultiply
  change eqToHom _ ≫ eqToHom _ ≫ (SyntheticCategory.biShift_comp (m,w) (0,0)).inv.app S_0_0 ≫
    SyntheticCategory.biShift_zero.hom.app (Smn m w) ≫ a = a
  dsimp only [Smn]
  erw [← hu]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]


end
end AssemblyShift


open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Core.SpectralSequence KIP126.Literature
namespace KIP126.Literature.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
private theorem product_first_quotient_label  (s t : ℤ)
    (y : (background.classical.sphere.Page 2 (s,t))) :
    (KIP126.AdamsSynthetic.sphereFirstQuotient background.nu background.quotients.functoriality background.firstQuotient) s t
      (KIP126.Literature.firstLabel background .sphere s t y ≫ XModLambdaN.map
        ((SyntheticCategory.biShift_zero.hom.app _) ≫ background.nu.unitIso.hom) 1) = y := by
  let e := SyntheticCategory.biShift_zero.app (background.nu.functor.obj SphereSpectrum) ≪≫ background.nu.unitIso
  let Q := (background.quotients.functoriality.functor 1).mapIso e
  let c : BiHom (t-s) t (XModLambdaN (KIP126.Literature.nuZero background .sphere) 1) ≃ₗ[ℤ] (background.classical.sphere.Page 2 (s,t)) :=
    Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z
      (XModLambdaN (KIP126.Literature.nuZero background .sphere) 1) ≃ₗ[ℤ] (background.classical.sphere.Page 2 (s,t)))
      (Int.add_zero t)) (background.firstQuotient .sphere 0 s t)
  change c ((KIP126.Literature.firstLabel background .sphere s t y ≫ Q.hom) ≫ Q.inv) = y
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have cast_symm (n m : ℤ) (h : n = m)
      (e : BiHom (t-s) n (XModLambdaN (KIP126.Literature.nuZero background .sphere) 1) ≃ₗ[ℤ]
        (background.classical.sphere.Page 2 (s,t))) (z : (background.classical.sphere.Page 2 (s,t))) :
      (congrArg (fun w => BiHom (t-s) w (XModLambdaN (KIP126.Literature.nuZero background .sphere) 1)) h).mp
          (e.symm z) =
        ((congrArg (fun w => BiHom (t-s) w (XModLambdaN (KIP126.Literature.nuZero background .sphere) 1) ≃ₗ[ℤ]
          (background.classical.sphere.Page 2 (s,t))) h).mp e).symm z := by
    subst m
    rfl
  have hc : KIP126.Literature.firstLabel background .sphere s t y = c.symm y := by
    exact cast_symm (t+0) t (Int.add_zero t) (background.firstQuotient .sphere 0 s t) y
  rw [hc,LinearEquiv.apply_symm_apply]


private theorem product_native_coordinate (s t : ℤ)
    (x : (background.classical.sphere.Page 2 (s,t))) :
    (KIP126.Literature.sphereFirstQuotient background s t)
      (nativeLabel .sphere s t x ≫ XModLambdaN.map background.nu.unitIso.hom 1) = x := by
  dsimp only [nativeLabel]
  rw [Category.assoc, ←background.quotients.functoriality.map_comp]
  exact product_first_quotient_label s t x

private theorem product_regrade_comp {m m' w w' : ℤ} {A B : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

private theorem product_diagonal_finite_action
    (q : ℕ) (hq : 0<q) (s t s' t' : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (a : BiHom ((t:ℤ)-s) t (S_0_0:SyntheticSpectrum))
    (b : BiHom ((t':ℤ)-s') t'
      (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : KIP126.Literature.sphereFirstQuotient background s t (quotientClass 1 a)=x)
    (hb : Detects (background.convergence (.quotient q (.nu .sphere))) (s',t',t')
      (finiteLabel .sphere q s' t' y) b) :
    Detects (background.convergence (.quotient q (.nu .sphere)))
      ((s+s':ℕ),(t+t':ℕ),(t+t':ℕ))
      (finiteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
        ((eqToHom (congrArg (background.classical.sphere.Page 2)
          (show ((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))=(((s+s':ℕ):ℤ),((t+t':ℕ):ℤ)) by
            simp only [Prod.mk_add_mk,Nat.cast_add])))
          (background.sphereAlgebra.product (s,t) (s',t') x y)))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]) (sphereAction a b)) := by
  let A := background.nu.functor.obj SphereSpectrum
  let rho := (background.quotients.tower A).rho 1 q hq
  let Q := XModLambdaN.map background.nu.unitIso.hom 1
  let c : BiHom (((t+t':ℕ):ℤ)-((s+s':ℕ):ℤ)) ((t+t':ℕ):ℤ) (XModLambdaN A q) :=
    homotopyRegrade (by simp only [Nat.cast_add]; omega)
      (by simp only [Nat.cast_add]) (sphereAction a b)
  obtain ⟨z,hz,hcz⟩ := finite_every_class_detected .sphere q hq ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) c
  have hb1 : b ≫ rho = nativeLabel .sphere s' t' y :=
    finite_detects_unique .sphere s' t' y _ _
      (finite_detects_rho .sphere q hq s' t' y b hb) (native_label_detects .sphere s' t' y)
  have hc1 : c ≫ rho = nativeLabel .sphere ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) z :=
    finite_detects_unique .sphere ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) z _ _
      (finite_detects_rho .sphere q hq ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) z c hcz)
      (native_label_detects .sphere ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) z)
  have hc : KIP126.Literature.sphereFirstQuotient background ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) ((c≫rho)≫Q)=z := by
    rw [hc1]
    exact product_native_coordinate ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) z
  have hcomp : (c≫rho)≫Q =
      homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]) (sphereAction a ((b≫rho)≫Q)) := by
    dsimp only [c]
    rw [←product_regrade_comp,←product_regrade_comp]
    simp only [sphereAction, Category.assoc]
  have hxy := first_quotient_action s t s' t' a ((b≫rho)≫Q)
  rw [ha,hb1,product_native_coordinate] at hxy
  rw [hcomp,hb1] at hc
  have he := hc.symm.trans hxy
  rw [he] at hcz
  exact hcz

end
end KIP126.Literature.Standard



namespace KIP126.Literature.Standard.FiniteActionHelper
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard.SelectedLifetimeConstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 6000000

private def nativeFiniteLabel (X : AdamsObject) (q : ℕ) (s t w : ℤ) (hw : w ≤ t)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :=
  (background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
    2 (s,t,w) (nuWeightLabel background X s t w hw x)

private def finiteLambdaClass (X : AdamsObject) (q k : ℕ) (hk : 0<k) (hkq : k<q)
    (s t w : ℤ)
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k))) :
    BiHom (t-s) (w-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
  homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
    (shiftHomotopyClass (0,-(k:ℤ)) (t-s,w) a) ≫
      ((background.quotients.tower _).triangle hk hkq).lambdaMap

private theorem finite_lambda_detects_general
    (X : AdamsObject) (q k : ℕ) (hk : 0<k) (hkq : k<q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < (q-k:ℕ))
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (ha : Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,w)
      (nativeFiniteLabel X (q-k) s t w (by omega) x) a) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,w-k)
      (nativeFiniteLabel X q s t (w-k) (by omega) x)
      (finiteLambdaClass X q k hk hkq s t w a) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let n := q-k
  have hn : 0<n := by dsimp [n]; omega
  have hsource : (s,t,w)=(s,(t-s)+s,w) := by simp
  have hstem := detects_transport hsource _ _ ha
  let L : ((SyntheticObject.shift (0,-(k:ℤ)) (.quotient n (.nu X))).obj background.nu background.auxiliary) ⟶
      ((SyntheticObject.quotient q (.nu X)).obj background.nu background.auxiliary) :=
    ((background.quotients.tower A).triangle hk hkq).lambdaMap
  have hmap := shifted_map_detects (.quotient n (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,w) s L _ a hstem
  have hindex : (s,((t-s,w)+(0,-(k:ℤ))).1+s,((t-s,w)+(0,-(k:ℤ))).2) =
      (s,t,w-k) := by ext <;> simp [sub_eq_add_neg]
  have hmap := detects_transport hindex _ _ hmap
  obtain ⟨e,he,ar,har,hgar⟩ := hmap
  obtain ⟨e0,he0,_⟩ := ha
  have heStem := representative_transport hsource _ _ he0
  have heMap := shifted_representative_map (.quotient n (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,w) s L _ _ heStem
  have heMap := representative_transport hindex _ _ heMap
  have heq := he.unique heMap
  have heq' : e = infinityFiniteLambda X q k hkq (s,t) w e0 := by
    convert heq using 1
    simp only [infinityFiniteLambda,
      InfinityShiftCoordinates.finiteLambdaMap, show k ≠ 0 by omega, ↓reduceDIte,
      InfinityShiftCoordinates.shift, infinityShift, Iso.trans_hom, ModuleCat.comp_apply,
      eqToIso.hom, infinityShiftData, infinityShift_comparison]
    rw [infinity_map_regrade L hindex]
    rfl
  have hs := (eInfinity_finite_labels X n hn s t w hw x e0).mp he0
  have hlabel : HasInfinityRepresentative _ 2 (s,t,w-k)
      (nativeFiniteLabel X q s t (w-k) (by omega) x)
      (infinityFiniteLambda X q k hkq (s,t) w e0) := by
    apply (eInfinity_finite_labels X q (by omega) s t (w-k)
      (by constructor <;> omega) x _).mpr
    refine ⟨?_, ?_⟩
    · convert hs.1 using 1
      dsimp [n] at *
      congr 1
      omega
    · rw [eInfinity_lambda_finite X q k hkq (s,t) w hw, hs.2]
      rfl
  refine ⟨e, ?_, ar, ?_, hgar⟩
  · change HasInfinityRepresentative (background.family.quotient A q) 2 (s,t,w-k)
      (nativeFiniteLabel X q s t (w-k) (by omega) x) e
    rw [heq']
    exact hlabel
  · convert har using 1
    simp only [finiteLambdaClass, regrade_precomp, Category.assoc]
    simp only [←Category.assoc, eqToHom_trans]
    rfl

private abbrev A := background.nu.functor.obj (SphereSpectrum : Spectrum)

private def pureTopIso (N r : ℕ) :
    (((SyntheticCategory.biShift (0,-(r:ℤ))).obj
      ((SyntheticCategory.biShift (0,-(N:ℤ))).obj A))⟦(1:ℤ)⟧) ≅
      Smn (Syn:=SyntheticSpectrum) 1 (-(N:ℤ)-r) :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (SyntheticCategory.biShift (1,0)).mapIso
      ((SyntheticCategory.biShift_comp (0,-(N:ℤ)) (0,-(r:ℤ))).app A) ≪≫
    (SyntheticCategory.biShift_comp ((0,-(N:ℤ))+(0,-(r:ℤ))) (1,0)).app A ≪≫
    eqToIso (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj A)
      (by ext <;> simp [sub_eq_add_neg])) ≪≫
    (SyntheticCategory.biShift (1,-(N:ℤ)-r)).mapIso background.nu.unitIso

private theorem pureLambdaMapExt (N r q : ℕ) (hq : 0<q)
    (hbound : (q:ℤ) ≤ 1+N+r)
    (f g : (SyntheticCategory.biShift (0,-(r:ℤ))).obj (XModLambdaN A N) ⟶
      XModLambdaN A q)
    (hfg : (SyntheticCategory.biShift (0,-(r:ℤ))).map (XModLambdaN.incl A N) ≫ f =
      (SyntheticCategory.biShift (0,-(r:ℤ))).map (XModLambdaN.incl A N) ≫ g) : f=g := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(r:ℤ))
  letI := background.exactness.shiftCommShift (0,-(r:ℤ))
  letI := background.exactness.shiftExact (0,-(r:ℤ))
  let T := F.mapTriangle.obj (XModLambdaN.cofiberTriangle A N)
  have hT : T ∈ distTriang SyntheticSpectrum :=
    F.map_distinguished _ (XModLambdaN.cofiberTriangle_distinguished A N)
  have hz : T.mor₂ ≫ (f-g)=0 := by
    change F.map (XModLambdaN.incl A N) ≫ (f-g)=0
    rw [Preadditive.comp_sub,hfg,sub_self]
  obtain ⟨u,hu⟩ := T.yoneda_exact₃ hT (f-g) hz
  have hu0 : u=0 := by
    let e := pureTopIso N r
    let z : BiHom 1 (-(N:ℤ)-r) (XModLambdaN A q) := e.inv ≫ u
    have hz0 : z=0 := selectedFiltration_finite_high_filtration_zero .sphere q hq
      1 (-(N:ℤ)-r) 0 (by omega) z
      (selectedFiltration_filtration_at_zero background.syntheticTower _ _ _ z)
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using hz0
  apply sub_eq_zero.mp
  rw [hu,hu0,comp_zero]

private theorem actualFiniteLambda (q k : ℕ) (hk : 0<k) (hkq : k<q) :
    lambdaPow k (XModLambdaN A q) =
      (SyntheticCategory.biShift (0,-(k:ℤ))).map
        ((background.quotients.tower A).rho (q-k) q (by omega)) ≫
      ((background.quotients.tower A).triangle hk hkq).lambdaMap := by
  apply pureLambdaMapExt q k q (by omega) (by omega)
  rw [←Category.assoc, ←Functor.map_comp,
    (background.quotients.tower A).rho_quotient (show q-k≤q by omega)]
  rw [((background.quotients.tower A).triangle hk hkq).lambda_quotient]
  exact lambdaPow_naturality k (XModLambdaN.incl A q)


private theorem finite_actual_lambda_detects
    (q k : ℕ) (hk : 0<k) (hkq : k<q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w+k < q)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : Detects (background.convergence (.quotient q (.nu .sphere))) (s,t,w)
      (nativeFiniteLabel .sphere q s t w (by omega) x) a) :
    Detects (background.convergence (.quotient q (.nu .sphere))) (s,t,w-k)
      (nativeFiniteLabel .sphere q s t (w-k) (by omega) x)
      (lambdaMultiply k a) := by
  let rho := (background.quotients.tower (background.nu.functor.obj SphereSpectrum)).rho (q-k) q (by omega)
  have hr := detects_map (.quotient q (.nu .sphere)) (.quotient (q-k) (.nu .sphere)) rho
    (s,t,w) _ _ ha
  change Detects (background.convergence (.quotient (q-k) (.nu .sphere))) (s,t,w)
    (background.family.pageMap rho 2 (s,t,w)
      (nativeFiniteLabel .sphere q s t w (by omega) x)) (a≫rho) at hr
  have hl := rhoFiniteLabelMap .sphere (q-k) q (by omega) s t w
    (nuWeightLabel background .sphere s t w (by omega) x)
  change background.family.pageMap rho 2 (s,t,w)
      (nativeFiniteLabel .sphere q s t w (by omega) x) =
    nativeFiniteLabel .sphere (q-k) s t w (by omega) x at hl
  have hr' : Detects (background.convergence (.quotient (q-k) (.nu .sphere))) (s,t,w)
      (nativeFiniteLabel .sphere (q-k) s t w (by omega) x) (a≫rho) :=
    Eq.mp (congrArg (fun z => Detects
      (background.convergence (.quotient (q-k) (.nu .sphere))) (s,t,w) z (a≫rho)) hl) hr
  have h := finite_lambda_detects_general .sphere q k hk hkq s t w
    (by constructor <;> omega) x (a≫rho) hr'

  have he : finiteLambdaClass .sphere q k hk hkq s t w (a≫rho) = lambdaMultiply k a := by
    simp only [finiteLambdaClass, regrade_precomp, shiftHomotopyClass, Functor.map_comp, Category.assoc]
    dsimp only [rho]
    erw [←actualFiniteLambda q k hk hkq]
    erw [lambdaPow_naturality]
    simp only [lambdaMultiply, ←Category.assoc]
    rfl
  rw [he] at h
  exact h


private theorem finite_action_zero_lambda (m w : ℤ) {X : SyntheticSpectrum} (a : BiHom m w X) :
    homotopyRegrade rfl (sub_zero w) (lambdaMultiply 0 a) = a := by
  have hu := background.quotients.coherence.right_unit (m,w) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,NatTrans.comp_app,eqToHom_app] at hu
  rw [regrade_precomp]
  delta lambdaMultiply
  change eqToHom _ ≫ eqToHom _ ≫ (SyntheticCategory.biShift_comp (m,w) (0,0)).inv.app S_0_0 ≫
    SyntheticCategory.biShift_zero.hom.app (Smn m w) ≫ a = a
  dsimp only [Smn]
  erw [← hu]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]

private theorem nativeFiniteDetects_regrade_iff
    (X : AdamsObject) (q : ℕ) (s t w u : ℤ) (hw : w≤t) (hu : u≤t)
    (h : w=u) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,w)
      (nativeFiniteLabel X q s t w hw x) a ↔
    Detects (background.convergence (.quotient q (.nu X))) (s,t,u)
      (nativeFiniteLabel X q s t u hu x) (homotopyRegrade rfl h a) := by
  subst u
  rfl

private theorem finite_actual_lambda_detects_all
    (q k : ℕ) (hkq : k<q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w+k < q)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : Detects (background.convergence (.quotient q (.nu .sphere))) (s,t,w)
      (nativeFiniteLabel .sphere q s t w (by omega) x) a) :
    Detects (background.convergence (.quotient q (.nu .sphere))) (s,t,w-k)
      (nativeFiniteLabel .sphere q s t (w-k) (by omega) x)
      (lambdaMultiply k a) := by
  by_cases hk : k=0
  · subst k
    apply (nativeFiniteDetects_regrade_iff .sphere q s t (w-(0:ℕ)) w
      (by omega) (by omega) (by simp) x (lambdaMultiply 0 a)).mpr
    rw [finite_action_zero_lambda]
    exact ha
  · exact finite_actual_lambda_detects q k (by omega) hkq s t w hw x a ha

private def finiteLambdaApply (X : AdamsObject) (q k : ℕ) (hkq : k<q)
    (s t w : ℤ)
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k))) :
    BiHom (t-s) (w-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) := by
  by_cases hk : k=0
  · subst k
    exact homotopyRegrade rfl (by omega) a
  · exact finiteLambdaClass X q k (by omega) hkq s t w a

private theorem finite_lambda_detects_all
    (X : AdamsObject) (q k : ℕ) (hkq : k<q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < (q-k:ℕ))
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (ha : Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,w)
      (nativeFiniteLabel X (q-k) s t w (by omega) x) a) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,w-k)
      (nativeFiniteLabel X q s t (w-k) (by omega) x)
      (finiteLambdaApply X q k hkq s t w a) := by
  by_cases hk : k=0
  · subst k
    exact (nativeFiniteDetects_regrade_iff X q s t w (w-(0:ℕ))
      (by omega) (by omega) (by simp) x a).mp ha
  · simpa only [finiteLambdaApply, dif_neg hk] using
      finite_lambda_detects_general X q k (by omega) hkq s t w hw x a ha

end
end KIP126.Literature.Standard.FiniteActionHelper







namespace KIP126.Literature.Standard.FiniteActionLocal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature.Standard
open KIP126.Literature.Standard.SelectedLifetimeConstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem local_regrade_cancel {m m' w w' : ℤ} {X : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (hm' : m'=m) (hw' : w'=w) (a : BiHom m w X) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a) = a := by
  subst m'; subst w'; rfl

private theorem local_shift_mem (X : SyntheticObject) (d p : ℤ×ℤ) (s : ℤ)
    (a : BiHom p.1 p.2 (X.obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (shiftHomotopyClass d p a) := by
  obtain ⟨ar,har⟩ := SelectedLifetimeConstruction.filtration_representative_exists
    (X.obj background.nu background.auxiliary) p s a ha
  let E := (KIP126.AdamsSynthetic.Completed.essShift d).filtered X p
  have hm : E.ambient.hom a ∈ ModuleCat.subobjectModule _
      ((background.convergence (.shift d X)).filtration.F s (p+d)) := by
    refine ⟨(E.level s).hom ar,?_⟩
    have he := ConcreteCategory.congr_hom (E.level_arrow s) ar
    simpa only [ModuleCat.comp_apply,har] using he
  rw [(KIP126.AdamsSynthetic.Completed.essShift d).ambient_eq X p] at hm
  simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
    OrderIso.apply_symm_apply,FiltrationAtLeast,SyntheticObject.obj,syntheticHomotopy,Prod.eta] using hm

private theorem local_normalized_action_filtration
    (N : ℕ) (hN : 0<N) (k l : ℕ) (m n s u : ℤ)
    (a : BiHom m (m+s) (S_0_0:SyntheticSpectrum))
    (b : BiHom n (n+u) (XModLambdaN (background.nu.functor.obj SphereSpectrum) N))
    {Z : SyntheticSpectrum}
    (L : (SyntheticCategory.biShift (0,-(l:ℤ))).obj
        (XModLambdaN (background.nu.functor.obj SphereSpectrum) N) ⟶ Z) :
    FiltrationAtLeast background.syntheticTower (s+u)
      (sphereAction (lambdaMultiply k a)
        (shiftHomotopyClass (0,-(l:ℤ)) (n,n+u) b ≫ L)) := by
  have hdiag : FiltrationAtLeast background.syntheticTower (s+u) (sphereAction a b) := by
    have h := finite_filtration_exhaustive .sphere N hN (s+u) (m+n+(s+u))
      (homotopyRegrade (by omega) (by omega) (sphereAction a b))
    have h' := selectedFiltration_regrade_filtration
      (by omega : (m+n+(s+u))-(s+u)=m+n)
      (by omega : m+n+(s+u)=(m+s)+(n+u)) (s+u) _ h
    rw [local_regrade_cancel] at h'
    exact h'
  have hlam := selectedFiltration_lambda_filtration k (s+u) (sphereAction a b) hdiag
  have hleft : FiltrationAtLeast background.syntheticTower (s+u)
      (sphereAction (lambdaMultiply k a) b) := by
    rw [AssemblyLambda.action_lambda_general background.quotients.coherence]
    exact selectedFiltration_regrade_filtration _ _ _ _ hlam
  have hshift := local_shift_mem (.quotient N (.nu .sphere)) (0,-(l:ℤ))
    (m+n, (m+s-(k:ℤ))+(n+u)) (s+u) _ hleft
  have hmap := selectedFiltration_map_filtration L _ _ (s+u) _ hshift
  rw [AssemblyShift.action_shift_postmap_general background.quotients.coherence]
  exact selectedFiltration_map_filtration L _ _ (s+u) _
    (selectedFiltration_regrade_filtration _ _ _ _ hshift)

end
end KIP126.Literature.Standard.FiniteActionLocal


namespace KIP126.Literature.Standard.FiniteActionFilteredQuotients
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.Literature.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
section Graded
universe u v w
variable {R : Type u} [Ring R] {ι : Type w}
  {A B : ι → ModuleCat.{v} R} {F : Filtration A} {G : Filtration B}
private theorem element_grade_equal_iff (F : Filtration A) (s : ℤ) (i : ι)
    (a b : (Subobject.underlying.obj (F.F s i) : ModuleCat R)) :
    F.toAssociatedGraded s i a = F.toAssociatedGraded s i b ↔
      (F.F s i).arrow a - (F.F s i).arrow b ∈
        (ModuleCat.subobjectModule (A i)) (F.F (s+1) i) := by
  simpa only [map_sub, sub_eq_zero] using
    F.toAssociatedGraded_eq_zero_iff s i (a-b)

private theorem graded_map_representative (f : FilteredMorphism F G) (s : ℤ) (i : ι)
    (a : (Subobject.underlying.obj (F.F s i) : ModuleCat R)) :
    f.inducedGrMap s i (F.toAssociatedGraded s i a) =
      G.toAssociatedGraded s i ((f.compat s i).choose a) := by
  have h : F.toAssociatedGraded s i ≫ f.inducedGrMap s i =
      (f.compat s i).choose ≫ G.toAssociatedGraded s i := by
    unfold Filtration.toAssociatedGraded FilteredMorphism.inducedGrMap
      Filtration.inducedAssocGradedMap
    dsimp only [cokernel.map]
    exact cokernel.π_desc _ _ _
  exact ConcreteCategory.congr_hom h a

/-- Being in the image on the graded piece means lifting modulo the next level. -/
private theorem graded_image_iff_lift (f : FilteredMorphism F G) (s : ℤ) (i : ι)
    (x : (Subobject.underlying.obj (G.F s i) : ModuleCat R)) :
    (∃ z : F.associatedGraded s i,
      f.inducedGrMap s i z = G.toAssociatedGraded s i x) ↔
    ∃ a : A i, a ∈ (ModuleCat.subobjectModule (A i)) (F.F s i) ∧
      (G.F s i).arrow x - f.map i a ∈
        (ModuleCat.subobjectModule (B i)) (G.F (s+1) i) := by
  have hc (a : (Subobject.underlying.obj (F.F s i) : ModuleCat R)) :
      f.map i ((F.F s i).arrow a) = (G.F s i).arrow ((f.compat s i).choose a) :=
    (ConcreteCategory.congr_hom (f.compat s i).choose_spec a).symm
  constructor
  · rintro ⟨z, hz⟩
    haveI : Epi (F.toAssociatedGraded s i) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s i)).mp inferInstance z
    refine ⟨(F.F s i).arrow a, ⟨a, rfl⟩, ?_⟩
    rw [hc]
    apply (element_grade_equal_iff G s i x _).mp
    rw [← graded_map_representative f s i a, ha, hz]
  · rintro ⟨_, ⟨a, rfl⟩, ha⟩
    refine ⟨F.toAssociatedGraded s i a, ?_⟩
    rw [hc] at ha
    rw [graded_map_representative]
    exact ((element_grade_equal_iff G s i x _).mpr ha).symm


end Graded
section Synthetic
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}
private def infinityGradedIso (c : SyntheticTowerConvergence P X) (p : ℤ × ℤ) (s : ℤ) :
    ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty ≅
      (P.filtration X).associatedGraded s p :=
  c.identification (s,p.1+s,p.2) ≪≫ eqToIso (by simp)


private theorem filtration_representative_exists (P : SyntheticTowerPresentation unit F)
    (A : Syn) (p : ℤ × ℤ) (s : ℤ) (a : BiHom p.1 p.2 A)
    (ha : a ∈ P.filtrationSubmodule A s p) :
    ∃ a' : (Subobject.underlying.obj ((P.filtration A).F s p) : ModuleCat.{v} ℤ),
      ((P.filtration A).F s p).arrow a' = a := by
  have hm : a ∈ ModuleCat.subobjectModule _ ((P.filtration A).F s p) := by
    simpa [SyntheticTowerPresentation.filtration, syntheticHomotopy] using ha
  exact hm


private theorem infinity_graded_naturality
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ) :
    (infinityGradedIso cx p s).hom ≫ M.filteredMap.inducedGrMap s p =
      (F.functor.map g).eInftyMap (s,p.1+s,p.2) ≫ (infinityGradedIso cy p s).hom := by
  have h := M.infinity_action_graded (s,p.1+s,p.2)
  have transport {ι : Type} (A B : ι → ModuleCat.{v} ℤ)
      (f : ∀ i, A i ⟶ B i) {i j : ι} (hij : i=j)
      {U V : ModuleCat.{v} ℤ} (a : U ⟶ A i) (b : V ⟶ B i)
      (q : U ⟶ V) (hq : a ≫ f i = q ≫ b) :
      (a ≫ eqToHom (congrArg A hij)) ≫ f j =
        q ≫ (b ≫ eqToHom (congrArg B hij)) := by
    subst j
    simpa only [eqToHom_refl,Category.comp_id] using hq
  exact transport
    (fun p => (P.filtration X).associatedGraded s p)
    (fun p => (P.filtration Y).associatedGraded s p)
    (fun p => M.filteredMap.inducedGrMap s p)
    (show (p.1+s-s,p.2)=p by ext <;> simp) _ _ _ h

private theorem infinity_image_iff_lift
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ)
    (x : (Subobject.underlying.obj ((P.filtration Y).F s p) : ModuleCat.{v} ℤ)) :
    (infinityGradedIso cy p s).inv ((P.filtration Y).toAssociatedGraded s p x) ∈
      Set.range ((F.functor.map g).eInftyMap (s,p.1+s,p.2)).hom ↔
    ∃ a : BiHom p.1 p.2 X, a ∈ P.filtrationSubmodule X s p ∧
      @HSub.hSub (BiHom p.1 p.2 Y) (BiHom p.1 p.2 Y) (BiHom p.1 p.2 Y)
        inferInstance (((P.filtration Y).F s p).arrow x) (a ≫ g) ∈
        P.filtrationSubmodule Y (s+1) p := by
  have hn := infinity_graded_naturality M p s
  have hi : (∃ z, (F.functor.map g).eInftyMap (s,p.1+s,p.2) z =
      (infinityGradedIso cy p s).inv ((P.filtration Y).toAssociatedGraded s p x)) ↔
      ∃ z, M.filteredMap.inducedGrMap s p z = (P.filtration Y).toAssociatedGraded s p x := by
    constructor
    · rintro ⟨z,hz⟩
      refine ⟨(infinityGradedIso cx p s).hom z,?_⟩
      have he := ConcreteCategory.congr_hom hn z
      change M.filteredMap.inducedGrMap s p ((infinityGradedIso cx p s).hom z) =
        (infinityGradedIso cy p s).hom ((F.functor.map g).eInftyMap (s,p.1+s,p.2) z) at he
      rw [hz] at he
      exact he.trans ((infinityGradedIso cy p s).toLinearEquiv.apply_symm_apply _)
    · rintro ⟨z,hz⟩
      refine ⟨(infinityGradedIso cx p s).inv z,?_⟩
      apply (infinityGradedIso cy p s).toLinearEquiv.injective
      have he := ConcreteCategory.congr_hom hn ((infinityGradedIso cx p s).inv z)
      simp only [ModuleCat.comp_apply] at he
      have ha := (infinityGradedIso cx p s).toLinearEquiv.apply_symm_apply z
      change (infinityGradedIso cx p s).hom ((infinityGradedIso cx p s).inv z) = z at ha
      rw [ha,hz] at he
      exact he.symm.trans ((infinityGradedIso cy p s).toLinearEquiv.apply_symm_apply _).symm
  change (∃ z, _ = _) ↔ _
  refine hi.trans ((graded_image_iff_lift M.filteredMap s p x).trans ?_)
  simp only [ConvergentMap.filteredMap_map,SyntheticTowerPresentation.filtration,
    OrderIso.apply_symm_apply]
  rfl


end Synthetic
private theorem subquotient_surjective_of_eq {R A : Type*} [Ring R]
    [AddCommGroup A] [Module R A] {Z Z' B B' : Submodule R A}
    (hZ : Z ≤ Z') (hB : B ≤ B') (h : Z=Z') :
    Function.Surjective (subquotientMap hZ hB) := by
  subst Z'
  exact subquotientMap_surjective hB

private theorem finite_lambda_coordinates_surjective (X : AdamsObject (coefficients := background.coefficients)) (m n : ℕ)
    (hnm : n < m) (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < (m-n : ℕ)) :
    Function.Surjective (KIP126.Literature.Standard.infinityFiniteLambda X m n hnm (s,t) w) := by
  have heq : (m:ℤ)-t+(w-n) = (m-n:ℕ)-t+w := by omega
  have hs : Function.Surjective
      (KIP126.Literature.quotientMap background X (c := (m-n:ℕ)-t+w) (c' := (m:ℤ)-t+(w-n))
        (b := 1+t-w) (b' := 1+t-(w-n)) (by omega) (by omega) (s,t)) := by
    exact subquotient_surjective_of_eq _
      (boundaries_monotone background X (s,t) (show 1+t-w ≤ 1+t-(w-n) by omega))
      (congrArg (fun c => KIP126.Literature.cycles background X c (s,t)) heq.symm)
  intro y
  obtain ⟨a,ha⟩ := hs (KIP126.Literature.Standard.infinityFiniteWindow X m (by omega)
    (s,t) (w-n) (by omega) y)
  refine ⟨(KIP126.Literature.Standard.infinityFiniteWindow X (m-n) (by omega)
    (s,t) w hw).symm a,?_⟩
  apply (KIP126.Literature.Standard.infinityFiniteWindow X m (by omega)
    (s,t) (w-n) (by omega)).injective
  rw [KIP126.Literature.Standard.eInfinity_lambda_finite X m n hnm (s,t) w hw]
  simpa only [AddEquiv.apply_symm_apply] using ha

private def lambda_source_infinity_iso (A : SyntheticObject (coefficients := background.coefficients)) (n : ℕ) (s t w : ℤ) :
    ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData (s,t,w+n)).eInfty ≅
      ((background.family.obj ((SyntheticObject.shift (0,-(n:ℤ)) A).obj background.nu background.auxiliary)).sequence.ssData
        (s,t,w)).eInfty := by
  simpa only [Prod.fst,Prod.snd,add_sub_cancel_right] using
    (infinityShift background KIP126.Literature.Standard.infinityShift_comparison A n (s,t) (w+n))

private theorem finite_lambda_infinity_surjective (X : AdamsObject (coefficients := background.coefficients)) (m n : ℕ)
    (hn : 0 < n) (hnm : n < m) (s t w : ℤ) (hw : (n:ℤ) ≤ t-w) :
    Function.Surjective ((background.family.map
      ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).triangle hn hnm).lambdaMap).eInftyMap
        (s,t,w)) := by
  by_cases htop : t-w < m
  · have hs := finite_lambda_coordinates_surjective X m n hnm s t (w+n) (by omega)
    have hh : Function.Surjective ((background.family.map
        ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).triangle hn hnm).lambdaMap).eInftyMap
          (s,t,(w+n)-n)) := by
      intro y
      obtain ⟨z,hz⟩ := hs y
      refine ⟨(infinityShift background KIP126.Literature.Standard.infinityShift_comparison
        (.quotient (m-n) (.nu X)) n (s,t) (w+n)).hom z,?_⟩
      simpa only [KIP126.Literature.Standard.infinityFiniteLambda,
        InfinityShiftCoordinates.finiteLambdaMap,show ¬ n=0 by omega,↓reduceDIte,
        KIP126.Literature.Standard.infinityShiftData,InfinityShiftCoordinates.shift,
        SyntheticAdamsFamily.quotient,SyntheticObject.obj,ModuleCat.comp_apply] using hz
    have he : w+(n:ℤ)-n=w := by omega
    exact he ▸ hh
  · have hz := selectedFiltration_finite_infinity_zero_outside X m (by omega) s t w (by omega)
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
    intro y
    exact ⟨0,@Subsingleton.elim _ hsub _ _⟩

private theorem finite_lambda_filtered_surjective (Y : AdamsObject (coefficients := background.coefficients)) (N A : ℕ)
    (hA : 0 < A) (hAN : A < N) (m w u : ℤ)
    (hwindow : (A : ℤ) ≤ m+u-w)
    (z : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hz : FiltrationAtLeast background.syntheticTower u z) :
    ∃ v : BiHom m w ((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-A))),
      FiltrationAtLeast background.syntheticTower u v ∧
      v ≫ ((background.quotients.tower _).triangle hA hAN).lambdaMap = z := by
  let X : SyntheticObject (coefficients := background.coefficients) := .shift (0,-(A:ℤ)) (.quotient (N-A) (.nu Y))
  let Z : SyntheticObject (coefficients := background.coefficients) := .quotient N (.nu Y)
  let f := ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).triangle hA hAN).lambdaMap
  let M := background.convergentMap X Z f
  let L : ℤ := N+w-m
  induction hd : (L-u).toNat using Nat.strong_induction_on generalizing u z with
  | h d ih =>
    by_cases htop : L ≤ u
    · have hzero : z=0 := selectedFiltration_finite_high_filtration_zero Y N (by omega) m w u
        (by dsimp [L] at htop; omega) z hz
      refine ⟨0, ?_, ?_⟩
      · exact (background.syntheticTower.filtrationSubmodule _ u (m,w)).zero_mem
      · simpa only [Limits.zero_comp] using hzero.symm
    · obtain ⟨zr,hzr⟩ := filtration_representative_exists background.syntheticTower
        (Z.obj background.nu background.auxiliary) (m,w) u z hz
      have hsurj := finite_lambda_infinity_surjective
        Y N A hA hAN u (m+u) w hwindow
      have hrange : (infinityGradedIso (background.convergence Z) (m,w) u).inv
          ((background.syntheticTower.filtration (Z.obj background.nu background.auxiliary)).toAssociatedGraded
            u (m,w) zr) ∈ Set.range ((background.family.functor.map f).eInftyMap
              (u,m+u,w)).hom := hsurj _
      obtain ⟨v,hv,hrem⟩ := (infinity_image_iff_lift M (m,w) u zr).mp hrange
      change BiHom m w ((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-A))) at v
      rw [hzr] at hrem
      have hd' : (L-(u+1)).toNat < d := by omega
      obtain ⟨v',hv',heq⟩ := ih (L-(u+1)).toNat hd' (u+1)
        (by omega) (z-v≫f) hrem rfl
      refine ⟨v+v', ?_, ?_⟩
      · exact (background.syntheticTower.filtrationSubmodule _ u (m,w)).add_mem hv
          (background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hv')
      · change (v+v')≫f=z
        rw [Preadditive.add_comp,heq]
        abel



end
end KIP126.Literature.Standard.FiniteActionFilteredQuotients
namespace KIP126.Literature.Standard.FiniteActionLocal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature.Standard KIP126.Literature.Standard.SelectedLifetimeConstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

private theorem local_regrade_postmap {m m' w w' : ℤ} {X Y : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w X) (f : X ⟶ Y) :
    homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

private theorem local_lambda_postmap {m w : ℤ} {X Y : SyntheticSpectrum}
    (k : ℕ) (a : BiHom m w X) (f : X ⟶ Y) :
    lambdaMultiply k (a≫f) = lambdaMultiply k a ≫ f := by
  simp only [lambdaMultiply,Category.assoc]

private theorem local_sphere_normal_form (m w s : ℤ) (h : w-m≤s)
    (a : BiHom m w (S_0_0:SyntheticSpectrum))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    ∃ a0 : BiHom m (m+s) (S_0_0:SyntheticSpectrum),
      homotopyRegrade rfl
        (by have := Int.toNat_of_nonneg (show 0≤m+s-w by omega); omega)
        (lambdaMultiply (m+s-w).toNat a0) = a := by
  have hmap := selectedFiltration_map_filtration background.nu.unitIso.inv m w s a ha
  obtain ⟨a0,ha0⟩ := (filtration_lambda .sphere m w s h (a≫background.nu.unitIso.inv)).mp hmap
  refine ⟨a0≫background.nu.unitIso.hom,?_⟩
  rw [local_lambda_postmap,local_regrade_postmap]
  change homotopyRegrade rfl _ (lambdaMultiply (m+s-w).toNat a0) = _ at ha0
  rw [ha0,Category.assoc,Iso.inv_hom_id,Category.comp_id]

end
end KIP126.Literature.Standard.FiniteActionLocal

namespace KIP126.Literature.Standard.FiniteActionLocal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature.Standard KIP126.Literature.Standard.SelectedLifetimeConstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

private theorem local_shift_zero (n z : ℤ) {X : SyntheticSpectrum} (b : BiHom n z X) :
    homotopyRegrade (add_zero n) (add_zero z)
      (shiftHomotopyClass (0,0) (n,z) b) ≫ SyntheticCategory.biShift_zero.hom.app X = b := by
  rw [←local_regrade_postmap]
  have hn := lambdaPow_naturality 0 b
  change (SyntheticCategory.biShift (0,0)).map b ≫ SyntheticCategory.biShift_zero.hom.app X =
    SyntheticCategory.biShift_zero.hom.app (Smn n z) ≫ b at hn
  unfold shiftHomotopyClass
  rw [Category.assoc,hn]
  have hu := background.quotients.coherence.right_unit (n,z) (S_0_0:SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app] at hu
  erw [←hu]
  rw [AssemblyShift.regrade_eq_comp]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc (SyntheticCategory.biShift_comp (n,z) (0,0))]
  rw [←Category.assoc,eqToHom_trans]
  simp only [eqToHom_refl,Category.id_comp]

private theorem local_sphere_normal_form_ex (m w s : ℤ) (h : w-m≤s)
    (a : BiHom m w (S_0_0:SyntheticSpectrum))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    ∃ (k : ℕ) (hk : m+s-(k:ℤ)=w) (a0 : BiHom m (m+s) (S_0_0:SyntheticSpectrum)),
      homotopyRegrade rfl hk (lambdaMultiply k a0) = a := by
  have hk : m+s-((m+s-w).toNat:ℤ)=w := by
    have := Int.toNat_of_nonneg (show 0≤m+s-w by omega);omega
  obtain ⟨a0,ha0⟩ := local_sphere_normal_form m w s h a ha
  exact ⟨_,hk,a0,ha0⟩

private theorem local_finite_normal_form (q : ℕ) (hq : 0<q) (n w u : ℤ)
    (h : w-n≤u)
    (b : BiHom n w (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (hb : FiltrationAtLeast background.syntheticTower u b) :
    b=0 ∨ ∃ (N l : ℕ) (_hN : 0<N) (hw : n+u-(l:ℤ)=w)
      (b0 : BiHom n (n+u) (XModLambdaN (background.nu.functor.obj SphereSpectrum) N))
      (L : (SyntheticCategory.biShift (0,-(l:ℤ))).obj
        (XModLambdaN (background.nu.functor.obj SphereSpectrum) N) ⟶
          XModLambdaN (background.nu.functor.obj SphereSpectrum) q),
      homotopyRegrade (by simp) (by dsimp; omega)
        (shiftHomotopyClass (0,-(l:ℤ)) (n,n+u) b0) ≫ L = b := by
  let l := (n+u-w).toNat
  have hl : (l:ℤ)=n+u-w := Int.toNat_of_nonneg (by omega)
  by_cases htop : q≤l
  · exact Or.inl (selectedFiltration_finite_high_filtration_zero .sphere q hq n w u (by omega) b hb)
  · right
    by_cases hl0 : l=0
    · have hw : w=n+u := by omega
      subst w
      refine ⟨q,0,hq,by omega,b,SyntheticCategory.biShift_zero.hom.app _,?_⟩
      exact local_shift_zero n (n+u) b
    · have hpos : 0<l := by omega
      have hlt : l<q := by omega
      obtain ⟨v,hv,hvb⟩ :=
        KIP126.Literature.Standard.FiniteActionFilteredQuotients.finite_lambda_filtered_surjective
          .sphere q l hpos hlt n w u (by omega) b hb
      let p : ℤ×ℤ := (n,n+u)
      let d : ℤ×ℤ := (0,-(l:ℤ))
      let X : SyntheticObject (coefficients := background.coefficients) := .quotient (q-l) (.nu .sphere)
      let E := (KIP126.AdamsSynthetic.Completed.essShift d).filtered X p
      let v' : BiHom (p+d).1 (p+d).2 ((SyntheticObject.shift d X).obj background.nu background.auxiliary) :=
        homotopyRegrade (by dsimp[p,d];omega) (by dsimp[p,d];omega) v
      let b0 : BiHom n (n+u) (XModLambdaN (background.nu.functor.obj SphereSpectrum) (q-l)) :=
        E.ambient.inv v'
      have he : shiftHomotopyClass d p b0 = v' := by
        rw [←(KIP126.AdamsSynthetic.Completed.essShift d).ambient_eq X p]
        exact Iso.inv_hom_id_apply E.ambient v'
      refine ⟨q-l,l,by omega,by omega,b0,
        ((background.quotients.tower _).triangle hpos hlt).lambdaMap,?_⟩
      change homotopyRegrade _ _ (shiftHomotopyClass d p b0) ≫ _ = b
      rw [he]
      change homotopyRegrade _ _ (homotopyRegrade _ _ v) ≫ _ = b
      rw [local_regrade_cancel]
      exact hvb

end
end KIP126.Literature.Standard.FiniteActionLocal

namespace KIP126.Literature.Standard.FiniteActionLocal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature.Standard KIP126.Literature.Standard.SelectedLifetimeConstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

private theorem local_action_regrade_left {m m' w w' n z : ℤ} {X : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w (S_0_0:SyntheticSpectrum)) (b : BiHom n z X) :
    sphereAction (homotopyRegrade hm hw a) b =
      homotopyRegrade (congrArg (fun r => r+n) hm) (congrArg (fun r => r+z) hw)
        (sphereAction a b) := by
  subst m';subst w';rfl

private theorem local_action_regrade_right {m w n n' z z' : ℤ} {X : SyntheticSpectrum}
    (hn : n=n') (hz : z=z') (a : BiHom m w (S_0_0:SyntheticSpectrum)) (b : BiHom n z X) :
    sphereAction a (homotopyRegrade hn hz b) =
      homotopyRegrade (congrArg (fun r => m+r) hn) (congrArg (fun r => w+r) hz)
        (sphereAction a b) := by
  subst n';subst z';rfl

private theorem local_action_filtration
    (q : ℕ) (hq : 0<q) (m w n z s u : ℤ) (haRange : w-m≤s) (hbRange : z-n≤u)
    (a : BiHom m w (S_0_0:SyntheticSpectrum))
    (b : BiHom n z (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (hb : FiltrationAtLeast background.syntheticTower u b) :
    FiltrationAtLeast background.syntheticTower (s+u) (sphereAction a b) := by
  obtain ⟨k,hk,a0,hfa⟩ := local_sphere_normal_form_ex m w s haRange a ha
  subst w
  change lambdaMultiply k a0 = a at hfa
  rw [←hfa]
  rcases local_finite_normal_form q hq n z u hbRange b hb with hb0 | ⟨N,l,hN,hw,b0,L,hfb⟩
  · rw [hb0]
    have he : sphereAction (lambdaMultiply k a0) (0 : BiHom n z
        (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))=0 := by
      simp only [sphereAction,comp_zero]
    rw [he]
    exact (background.syntheticTower.filtrationSubmodule _ _ _).zero_mem
  · subst z
    rw [←hfb,←local_regrade_postmap,local_action_regrade_right]
    apply selectedFiltration_regrade_filtration
    exact local_normalized_action_filtration N hN k l m n s u a0 b0 L

end
end KIP126.Literature.Standard.FiniteActionLocal

namespace KIP126.Literature.Standard.FiniteActionAssembly
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard KIP126.Literature.Standard.SelectedLifetimeConstruction
open KIP126.Literature.Standard.FiniteActionHelper
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

private theorem canonicalSphere (s t : ℤ) (k : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.permanentCycles background .sphere (s,t)) :
    ∃ a0 : BiHom (t-s) t (S_0_0:SyntheticSpectrum),
      KIP126.Literature.sphereFirstQuotient background s t (quotientClass 1 a0)=x ∧
      Detects (background.convergence .sphere) (s,t,t-k)
        (background.comparison.sphereE2 s t k x) (lambdaMultiply k a0) := by
  obtain ⟨a,ha⟩ := detects_lift_exists .sphere s t x hx
  let a0 := a≫background.nu.unitIso.hom
  have hc : KIP126.Literature.sphereFirstQuotient background s t (quotientClass 1 a0)=x := by
    rw [sphereNu_diagonal_first_projection s t x a ha]
    exact product_native_coordinate s t x
  refine ⟨a0,hc,?_⟩
  have hd := background.sphereDetectionCompatible.homotopy_lambda s t k a0
  change KIP126.AdamsSynthetic.sphereFirstQuotient background.nu background.quotients.functoriality
    background.firstQuotient s t (quotientClass 1 a0)=x at hc
  rw [hc] at hd
  exact hd

private theorem assembly_regrade_heq {m m' w w' : ℤ} {X : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w X) :
    HEq (homotopyRegrade hm hw a) a := by
  subst m'; subst w'; rfl

private theorem assembly_regrade_post_heq {m m' w w' : ℤ} {X Y : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w X) (f : X ⟶ Y) :
    HEq (homotopyRegrade hm hw a ≫ f) (a≫f) := by
  subst m'; subst w'; rfl

private theorem assembly_action_regrade_post_heq {m w n n' z z' : ℤ} {X Y : SyntheticSpectrum}
    (hn : n=n') (hz : z=z') (a : BiHom m w (S_0_0:SyntheticSpectrum))
    (b : BiHom n z X) (f : X ⟶ Y) :
    HEq (sphereAction a (homotopyRegrade hn hz b ≫ f)) (sphereAction a (b≫f)) := by
  subst n'; subst z'; rfl

private theorem assembly_action_regrade_right_heq {m w n n' z z' : ℤ} {X : SyntheticSpectrum}
    (hn : n=n') (hz : z=z') (a : BiHom m w (S_0_0:SyntheticSpectrum))
    (b : BiHom n z X) :
    HEq (sphereAction a (homotopyRegrade hn hz b)) (sphereAction a b) := by
  subst n'; subst z'; rfl

private theorem assembly_shift_regrade_post_heq {m m' w w' : ℤ} {X Y : SyntheticSpectrum}
    (δ : ℤ×ℤ) (hm : m=m') (hw : w=w') (a : BiHom m w X)
    (f : (SyntheticCategory.biShift δ).obj X ⟶ Y) :
    HEq (shiftHomotopyClass δ (m',w') (homotopyRegrade hm hw a) ≫ f)
      (shiftHomotopyClass δ (m,w) a ≫ f) := by
  subst m'; subst w'; rfl

private theorem action_finiteLambdaApply
    (q l : ℕ) (hlq : l<q) (s t s' t' : ℕ) (w : ℤ)
    (a : BiHom ((t:ℤ)-s) w (S_0_0:SyntheticSpectrum))
    (b : BiHom ((t':ℤ)-s') t'
      (XModLambdaN (background.nu.functor.obj SphereSpectrum) (q-l))) :
    homotopyRegrade (by simp only [Nat.cast_add]; omega) (by omega)
      (sphereAction a (finiteLambdaApply .sphere q l hlq s' t' t' b)) =
    finiteLambdaApply .sphere q l hlq ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) (w+t')
      (homotopyRegrade (by simp only [Nat.cast_add]; omega) rfl (sphereAction a b)) := by
  by_cases hl : l=0
  · subst l
    simp only [finiteLambdaApply, ↓reduceDIte]
    apply eq_of_heq
    refine (assembly_regrade_heq _ _ _).trans ?_
    refine (assembly_action_regrade_right_heq _ _ a b).trans ?_
    apply HEq.symm
    refine (assembly_regrade_heq _ _ _).trans ?_
    exact assembly_regrade_heq _ _ _
  · let L := ((background.quotients.tower (background.nu.functor.obj SphereSpectrum)).triangle
        (show 0<l by omega) hlq).lambdaMap
    have h := AssemblyShift.action_shift_postmap_general background.quotients.coherence
      (0,-(l:ℤ)) ((t:ℤ)-s) w ((t':ℤ)-s') t' a b L
    simp only [finiteLambdaApply, hl, ↓reduceDIte, finiteLambdaClass]
    apply eq_of_heq
    refine (assembly_regrade_heq _ _ _).trans ?_
    refine (assembly_action_regrade_post_heq _ _ a
      (shiftHomotopyClass (0,-(l:ℤ)) ((t':ℤ)-s',t') b) L).trans ?_
    refine (heq_of_eq h).trans ?_
    refine (assembly_regrade_post_heq _ _ _ L).trans ?_
    apply HEq.symm
    refine (assembly_regrade_post_heq _ _ _ L).trans ?_
    exact assembly_shift_regrade_post_heq (0,-(l:ℤ)) _ _ (sphereAction a b) L

private theorem finite_apply_regrade_heq (X : AdamsObject) (q l : ℕ) (hlq : l<q)
    (s t w w' : ℤ) (h : w=w')
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-l))) :
    HEq (finiteLambdaApply X q l hlq s t w' (homotopyRegrade rfl h a))
      (finiteLambdaApply X q l hlq s t w a) := by
  subst w'
  rfl

private theorem lambda_heq (k : ℕ) {m m' w w' : ℤ} {X : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w X) (b : BiHom m' w' X) (h : HEq a b) :
    HEq (lambdaMultiply k a) (lambdaMultiply k b) := by
  subst m'; subst w'
  cases eq_of_heq h
  rfl

private theorem canonical_product_detects
    (q k l : ℕ) (hklq : k+l<q) (s t s' t' : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (a0 : BiHom ((t:ℤ)-s) t (S_0_0:SyntheticSpectrum))
    (b0 : BiHom ((t':ℤ)-s') t' (XModLambdaN (background.nu.functor.obj SphereSpectrum) (q-l)))
    (ha0 : KIP126.Literature.sphereFirstQuotient background s t (quotientClass 1 a0)=x)
    (hb0 : Detects (background.convergence (.quotient (q-l) (.nu .sphere))) (s',t',t')
      (nativeFiniteLabel .sphere (q-l) s' t' t' (by omega) y) b0) :
    Detects (background.convergence (.quotient q (.nu .sphere)))
      ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
      (nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
        (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega)
        ((eqToHom (congrArg (background.classical.sphere.Page 2)
          (show ((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))=(((s+s':ℕ):ℤ),((t+t':ℕ):ℤ)) by
            simp only [Prod.mk_add_mk,Nat.cast_add])))
          (background.sphereAlgebra.product (s,t) (s',t') x y)))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega)
        (sphereAction (lambdaMultiply k a0)
          (finiteLambdaApply .sphere q l (by omega) s' t' t' b0))) := by
  let S : ℤ := ((s+s':ℕ):ℤ)
  let T : ℤ := ((t+t':ℕ):ℤ)
  let Z := (eqToHom (congrArg (background.classical.sphere.Page 2)
      (show ((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))=(S,T) by
        dsimp only [S,T]; simp only [Prod.mk_add_mk,Nat.cast_add])))
      (background.sphereAlgebra.product (s,t) (s',t') x y)
  let c : BiHom (T-S) T (XModLambdaN (background.nu.functor.obj SphereSpectrum) (q-l)) :=
    homotopyRegrade (by dsimp only [S,T]; simp only [Nat.cast_add]; omega)
      (by dsimp only [T]; simp only [Nat.cast_add]) (sphereAction a0 b0)
  have hd := product_diagonal_finite_action (q-l) (by omega) s t s' t' x y a0 b0 ha0 hb0
  change Detects (background.convergence (.quotient (q-l) (.nu .sphere))) (S,T,T)
    (nativeFiniteLabel .sphere (q-l) S T T (by omega) Z) c at hd
  let d := finiteLambdaApply .sphere q l (by omega) S T T c
  have hL := finite_lambda_detects_all .sphere q l (by omega) S T T (by constructor <;> omega) Z c hd
  change Detects (background.convergence (.quotient q (.nu .sphere))) (S,T,T-l)
    (nativeFiniteLabel .sphere q S T (T-l) (by omega) Z) d at hL
  have hK := finite_actual_lambda_detects_all q k (by omega) S T (T-l)
    (by constructor <;> omega) Z d hL
  have ht : (T-l)-k=T-(k+l:ℕ) := by simp only [Nat.cast_add]; omega
  have hK' := (nativeFiniteDetects_regrade_iff .sphere q S T ((T-l)-k) (T-(k+l:ℕ))
    (by omega) (by omega) ht Z (lambdaMultiply k d)).mp hK
  let B := finiteLambdaApply .sphere q l (by omega) s' t' t' b0
  have hraw : HEq (sphereAction a0 B) d := by
    have h := action_finiteLambdaApply q l (by omega) s t s' t' t a0 b0
    refine (assembly_regrade_heq
      (show ((t:ℤ)-s)+((t':ℤ)-s')=T-S by dsimp only [S,T]; simp only [Nat.cast_add]; omega)
      (show (t:ℤ)+((t':ℤ)-l)=((t:ℤ)+t')-l by omega) (sphereAction a0 B)).symm.trans ?_
    refine (heq_of_eq h).trans ?_
    apply HEq.symm
    exact finite_apply_regrade_heq .sphere q l (by omega) S T ((t:ℤ)+t') T
      (by dsimp only [T]; simp only [Nat.cast_add])
      (homotopyRegrade (by dsimp only [S,T]; simp only [Nat.cast_add]; omega) rfl (sphereAction a0 b0))
  have hlam := AssemblyLambda.action_lambda_general background.quotients.coherence
    k ((t:ℤ)-s) t ((t':ℤ)-s') ((t':ℤ)-l) a0 B
  have heq : homotopyRegrade (by dsimp only [S,T]; simp only [Nat.cast_add]; omega)
        (by dsimp only [T]; simp only [Nat.cast_add]; omega)
        (sphereAction (lambdaMultiply k a0) B) =
      homotopyRegrade rfl ht (lambdaMultiply k d) := by
    apply eq_of_heq
    refine (assembly_regrade_heq _ _ _).trans ?_
    refine (heq_of_eq hlam).trans ?_
    refine (assembly_regrade_heq _ _ _).trans ?_
    refine (lambda_heq k (by dsimp only [S,T]; simp only [Nat.cast_add]; omega)
      (by dsimp only [T]; simp only [Nat.cast_add]; omega) _ _ hraw).trans ?_
    exact (assembly_regrade_heq _ _ _).symm
  rw [←heq] at hK'
  exact hK'

private theorem assembly_detects_filtration
    (X : SyntheticObject (coefficients:=background.coefficients)) (i : Tridegree)
    (x : (background.family.obj (X.obj background.nu background.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence X) i x a) :
    FiltrationAtLeast background.syntheticTower i.1 a := by
  obtain ⟨e,he,b,hb,hgr⟩ := ha
  have hm : ((background.syntheticTower.filtration (X.obj background.nu background.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow b ∈ ModuleCat.subobjectModule _
      ((background.syntheticTower.filtration (X.obj background.nu background.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)) := ⟨b,rfl⟩
  rw [hb] at hm
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm

private theorem assembly_regrade_sub {m m' w w' : ℤ} {X : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a b : BiHom m w X) :
    homotopyRegrade hm hw (a-b)=homotopyRegrade hm hw a-homotopyRegrade hm hw b := by
  subst m'; subst w'; rfl

private theorem native_product_stable
    (q : ℕ) (hq : 0<q) (s t s' t' k l : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (z : background.classical.sphere.Page 2 ((s+s':ℕ),(t+t':ℕ)))
    (a A : BiHom ((t:ℤ)-s) ((t:ℤ)-k) (S_0_0:SyntheticSpectrum))
    (b B : BiHom ((t':ℤ)-s') ((t':ℤ)-l)
      (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : Detects (background.convergence .sphere) (s,t,(t:ℤ)-k)
      (background.comparison.sphereE2 s t k x) a)
    (hA : Detects (background.convergence .sphere) (s,t,(t:ℤ)-k)
      (background.comparison.sphereE2 s t k x) A)
    (hb : Detects (background.convergence (.quotient q (.nu .sphere))) (s',t',(t':ℤ)-l)
      (nativeFiniteLabel .sphere q s' t' ((t':ℤ)-l) (by omega) y) b)
    (hB : Detects (background.convergence (.quotient q (.nu .sphere))) (s',t',(t':ℤ)-l)
      (nativeFiniteLabel .sphere q s' t' ((t':ℤ)-l) (by omega) y) B)
    (hP : Detects (background.convergence (.quotient q (.nu .sphere)))
      ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
      (nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
        (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega) z)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction A B))) :
    Detects (background.convergence (.quotient q (.nu .sphere)))
      ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
      (nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
        (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega) z)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b)) := by
  let X : SyntheticObject (coefficients:=background.coefficients) := .quotient q (.nu .sphere)
  have had := detects_sub_filtration (background.convergence .sphere) (s,t,(t:ℤ)-k) ha hA
  have hbd := detects_sub_filtration (background.convergence X) (s',t',(t':ℤ)-l) hb hB
  have hbf := assembly_detects_filtration X (s',t',(t':ℤ)-l) _ b hb
  have hAf := assembly_detects_filtration .sphere (s,t,(t:ℤ)-k) _ A hA
  have h1 : FiltrationAtLeast background.syntheticTower (((s+s':ℕ):ℤ)+1)
      (sphereAction (a-A) b) := by
    rw [show (((s+s':ℕ):ℤ)+1)=((s:ℤ)+1)+s' by omega]
    exact FiniteActionLocal.local_action_filtration q hq ((t:ℤ)-s) ((t:ℤ)-k) ((t':ℤ)-s') ((t':ℤ)-l)
      ((s:ℤ)+1) s' (by omega) (by omega) (a-A) b had hbf
  have h2 : FiltrationAtLeast background.syntheticTower (((s+s':ℕ):ℤ)+1)
      (sphereAction A (b-B)) := by
    rw [show (((s+s':ℕ):ℤ)+1)=(s:ℤ)+((s':ℤ)+1) by omega]
    exact FiniteActionLocal.local_action_filtration q hq ((t:ℤ)-s) ((t:ℤ)-k) ((t':ℤ)-s') ((t':ℤ)-l)
      s ((s':ℤ)+1) (by omega) (by omega) A (b-B) hAf hbd
  have hsum := (background.syntheticTower.filtrationSubmodule (X.obj background.nu background.auxiliary)
    (((s+s':ℕ):ℤ)+1) _).add_mem h1 h2
  have he : sphereAction (a-A) b+sphereAction A (b-B)=sphereAction a b-sphereAction A B := by
    letI := background.exactness.shiftAdditive (((t':ℤ)-s'),((t':ℤ)-l))
    simp only [sphereAction,Functor.map_sub,Preadditive.sub_comp,Preadditive.comp_sub]
    abel
  rw [he] at hsum
  have hc := selectedFiltration_regrade_filtration
    (show ((t:ℤ)-s)+((t':ℤ)-s')=((t+t':ℕ):ℤ)-((s+s':ℕ):ℤ) by simp only [Nat.cast_add]; omega)
    (show ((t:ℤ)-k)+((t':ℤ)-l)=((t+t':ℕ):ℤ)-(k+l:ℕ) by simp only [Nat.cast_add]; omega)
    (((s+s':ℕ):ℤ)+1) _ hsum
  rw [assembly_regrade_sub] at hc
  exact KIP126.AdamsSynthetic.detects_of_sub_filtration _ _ hP hc

private theorem native_product_outside
    (q : ℕ) (hq : 0<q) (s t s' t' k l : ℕ) (hout : q≤k+l)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (z : background.classical.sphere.Page 2 ((s+s':ℕ),(t+t':ℕ)))
    (a : BiHom ((t:ℤ)-s) ((t:ℤ)-k) (S_0_0:SyntheticSpectrum))
    (b : BiHom ((t':ℤ)-s') ((t':ℤ)-l)
      (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : Detects (background.convergence .sphere) (s,t,(t:ℤ)-k)
      (background.comparison.sphereE2 s t k x) a)
    (hb : Detects (background.convergence (.quotient q (.nu .sphere))) (s',t',(t':ℤ)-l)
      (nativeFiniteLabel .sphere q s' t' ((t':ℤ)-l) (by omega) y) b) :
    Detects (background.convergence (.quotient q (.nu .sphere)))
      ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
      (nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
        (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega) z)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b)) := by
  let X : SyntheticObject (coefficients:=background.coefficients) := .quotient q (.nu .sphere)
  let c := homotopyRegrade
    (show ((t:ℤ)-s)+((t':ℤ)-s')=((t+t':ℕ):ℤ)-((s+s':ℕ):ℤ) by simp only [Nat.cast_add]; omega)
    (show ((t:ℤ)-k)+((t':ℤ)-l)=((t+t':ℕ):ℤ)-(k+l:ℕ) by simp only [Nat.cast_add]; omega)
    (sphereAction a b)
  have haf := assembly_detects_filtration .sphere (s,t,(t:ℤ)-k) _ a ha
  have hbf := assembly_detects_filtration X (s',t',(t':ℤ)-l) _ b hb
  have hf := FiniteActionLocal.local_action_filtration q hq ((t:ℤ)-s) ((t:ℤ)-k) ((t':ℤ)-s') ((t':ℤ)-l)
    s s' (by omega) (by omega) a b haf hbf
  have hfc : FiltrationAtLeast background.syntheticTower ((s:ℤ)+s') c :=
    selectedFiltration_regrade_filtration _ _ _ _ hf
  have hcz : c=0 := selectedFiltration_finite_high_filtration_zero .sphere q hq
    (((t+t':ℕ):ℤ)-((s+s':ℕ):ℤ)) (((t+t':ℕ):ℤ)-(k+l:ℕ)) ((s:ℤ)+s')
    (by omega) c hfc
  have hzE := finite_quotient_vanishing .sphere q hq 2 (by decide)
    ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) (((t+t':ℕ):ℤ)-(k+l:ℕ)) (Or.inr (by omega))
  letI : Subsingleton ((background.family.quotient
      (background.nu.functor.obj SphereSpectrum) q).E₂
        ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))) :=
    ModuleCat.isZero_iff_subsingleton.mp hzE
  have hlabel : nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
      (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega) z=0 :=
    @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp hzE) _ _
  change Detects (background.convergence (.quotient q (.nu .sphere)))
    ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
    (nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
      (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega) z) c
  rw [hlabel,hcz]
  exact ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,0,map_zero _,by simp only [map_zero]⟩

private def assemblyProductLabel (s t s' t' : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t')) :=
  (eqToHom (congrArg (background.classical.sphere.Page 2)
    (show ((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))=(((s+s':ℕ):ℤ),((t+t':ℕ):ℤ)) by
      simp only [Prod.mk_add_mk,Nat.cast_add])))
    (background.sphereAlgebra.product (s,t) (s',t') x y)

private theorem native_product_inside
    (q : ℕ) (hq : 0<q) (s t s' t' k l : ℕ) (hklq : k+l<q)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (a : BiHom ((t:ℤ)-s) ((t:ℤ)-k) (S_0_0:SyntheticSpectrum))
    (b : BiHom ((t':ℤ)-s') ((t':ℤ)-l)
      (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : Detects (background.convergence .sphere) (s,t,(t:ℤ)-k)
      (background.comparison.sphereE2 s t k x) a)
    (hb : Detects (background.convergence (.quotient q (.nu .sphere))) (s',t',(t':ℤ)-l)
      (nativeFiniteLabel .sphere q s' t' ((t':ℤ)-l) (by omega) y) b) :
    Detects (background.convergence (.quotient q (.nu .sphere)))
      ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
      (nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
        (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega) (assemblyProductLabel s t s' t' x y))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b)) := by
  have haNu := sphereNu_detects_forward s t k x a ha
  obtain ⟨ea,hea,_⟩ := haNu
  have hx := ((eInfinity_nu_labels .sphere s t ((t:ℤ)-k) (by omega) x ea).mp hea).1
  obtain ⟨a0,hcoord,hak⟩ := canonicalSphere s t k x hx
  have hbCopy := hb
  obtain ⟨eb,heb,_⟩ := hbCopy
  have hy : y ∈ KIP126.Literature.cycles background .sphere (q-l:ℕ) (s',t') := by
    have h := ((eInfinity_finite_labels .sphere q hq s' t' ((t':ℤ)-l)
      (by constructor <;> omega) y eb).mp heb).1
    have hi : ((q-l:ℕ):ℤ)=(q:ℤ)-t'+((t':ℤ)-l) := by omega
    rw [hi]
    exact h
  obtain ⟨b0,hb0⟩ := finite_detected_class .sphere (q-l) (by omega) s' t' y hy
  change Detects (background.convergence (.quotient (q-l) (.nu .sphere))) (s',t',t')
    (nativeFiniteLabel .sphere (q-l) s' t' t' (by omega) y) b0 at hb0
  have hB := finite_lambda_detects_all .sphere q l (by omega) s' t' t'
    (by constructor <;> omega) y b0 hb0
  have hP := canonical_product_detects q k l hklq s t s' t' x y a0 b0 hcoord hb0
  exact native_product_stable q hq s t s' t' k l x y (assemblyProductLabel s t s' t' x y)
    a (lambdaMultiply k a0) b (finiteLambdaApply .sphere q l (by omega) s' t' t' b0)
    ha hak hb hB hP

private theorem native_product_all
    (q : ℕ) (hq : 0<q) (s t s' t' k l : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (a : BiHom ((t:ℤ)-s) ((t:ℤ)-k) (S_0_0:SyntheticSpectrum))
    (b : BiHom ((t':ℤ)-s') ((t':ℤ)-l)
      (XModLambdaN (background.nu.functor.obj SphereSpectrum) q))
    (ha : Detects (background.convergence .sphere) (s,t,(t:ℤ)-k)
      (background.comparison.sphereE2 s t k x) a)
    (hb : Detects (background.convergence (.quotient q (.nu .sphere))) (s',t',(t':ℤ)-l)
      (nativeFiniteLabel .sphere q s' t' ((t':ℤ)-l) (by omega) y) b) :
    Detects (background.convergence (.quotient q (.nu .sphere)))
      ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
      (nativeFiniteLabel .sphere q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ)
        (((t+t':ℕ):ℤ)-(k+l:ℕ)) (by omega) (assemblyProductLabel s t s' t' x y))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b)) := by
  by_cases h : k+l<q
  · exact native_product_inside q hq s t s' t' k l h x y a b ha hb
  · exact native_product_outside q hq s t s' t' k l (by omega) x y _ a b ha hb

end
end KIP126.Literature.Standard.FiniteActionAssembly

namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Core.SpectralSequence
open KIP126.Literature.Standard.SelectedLifetimeConstruction
open KIP126.Literature.Standard.FiniteActionHelper
open KIP126.Literature.Standard.FiniteActionAssembly
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
private theorem wrapper_sphere_label_transport (s t u v : ℤ) (hs:s=u) (ht:t=v) (k:ℕ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    HEq (background.comparison.sphereE2 u v k
      ((eqToHom (congrArg (background.classical.sphere.Page 2) (Prod.ext hs ht))) x))
      (background.comparison.sphereE2 s t k x) := by
  subst u
  subst v
  rfl

private theorem finite_action_complete (q : ℕ) (hq : 0 < q) (s t s' t' k l : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (a : BiHom ((t : ℤ)-s) ((t : ℤ)-k) (S_0_0 : SyntheticSpectrum))
    (b : BiHom ((t' : ℤ)-s') ((t' : ℤ)-l) (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : Detects (background.convergence .sphere) (s,t,(t : ℤ)-k) (background.comparison.sphereE2 s t k x) a)
    (hb : Detects (background.convergence (.quotient q .sphere)) (s',t',(t' : ℤ)-l)
      ((background.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        (s',t',(t' : ℤ)-l) (background.comparison.sphereE2 s' t' l y)) b) :
    Detects (background.convergence (.quotient q .sphere))
      ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
      ((background.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
        (background.comparison.sphereE2 (s+s') (t+t') (k+l)
          (by simpa only [Nat.cast_add, Prod.mk_add_mk] using
            background.sphereAlgebra.product (s,t) (s',t') x y)))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b))  := by
  let V := background.nu.functor.obj SphereSpectrum
  let Q := sphereNu_quotientIso q
  let bNu := b ≫ Q.hom
  have hbNu := sphereNu_finite_detects_forward q s' t' l y b hb
  have hprod := native_product_all q hq s t s' t' k l x y a bNu ha hbNu
  have hout := sphereNu_finite_detects_reverse q ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) (k+l)
    (assemblyProductLabel s t s' t' x y)
    (homotopyRegrade (by simp only [Nat.cast_add]; omega)
      (by simp only [Nat.cast_add]; omega) (sphereAction a bNu)) hprod
  have hc : homotopyRegrade (show ((t:ℤ)-s)+((t':ℤ)-s')=((t+t':ℕ):ℤ)-((s+s':ℕ):ℤ) by simp only [Nat.cast_add]; omega)
        (show ((t:ℤ)-k)+((t':ℤ)-l)=((t+t':ℕ):ℤ)-((k+l:ℕ):ℤ) by simp only [Nat.cast_add]; omega) (sphereAction a bNu) ≫ Q.inv =
      homotopyRegrade (show ((t:ℤ)-s)+((t':ℤ)-s')=((t+t':ℕ):ℤ)-((s+s':ℕ):ℤ) by simp only [Nat.cast_add]; omega)
        (show ((t:ℤ)-k)+((t':ℤ)-l)=((t+t':ℕ):ℤ)-((k+l:ℕ):ℤ) by simp only [Nat.cast_add]; omega) (sphereAction a b) := by
    rw [←product_regrade_comp]
    dsimp only [sphereAction,bNu]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  change Detects (background.convergence (.quotient q .sphere))
    ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
    ((background.family.quotientProjection (S_0_0:SyntheticSpectrum) q).pageMap 2
      ((s+s':ℕ),(t+t':ℕ),((t+t':ℕ):ℤ)-(k+l:ℕ))
      (background.comparison.sphereE2 ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) (k+l)
        (assemblyProductLabel s t s' t' x y)))
    (homotopyRegrade (by simp only [Nat.cast_add]; omega)
      (by simp only [Nat.cast_add]; omega) (sphereAction a bNu) ≫ Q.inv) at hout
  rw [hc] at hout
  have hlabel := wrapper_sphere_label_transport ((s:ℤ)+s') ((t:ℤ)+t')
    ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) (by simp only [Nat.cast_add]) (by simp only [Nat.cast_add])
    (k+l) (background.sphereAlgebra.product (s,t) (s',t') x y)
  change HEq (background.comparison.sphereE2 ((s+s':ℕ):ℤ) ((t+t':ℕ):ℤ) (k+l)
    (assemblyProductLabel s t s' t' x y))
    (background.comparison.sphereE2 ((s:ℤ)+s') ((t:ℤ)+t') (k+l)
      (background.sphereAlgebra.product (s,t) (s',t') x y)) at hlabel
  rw [eq_of_heq hlabel] at hout
  exact hout

end
end KIP126.Literature.Standard

namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Core.SpectralSequence
open KIP126.Literature.Standard.SelectedLifetimeConstruction
open KIP126.Literature.Standard.FiniteActionHelper
open KIP126.Literature.Standard.FiniteActionAssembly
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
/-- Detection of the sphere action on every positive finite lambda quotient,
with all natural-number weight indices. -/
public theorem finite_action (q : ℕ) (hq : 0 < q) (s t s' t' k l : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (a : BiHom ((t : ℤ)-s) ((t : ℤ)-k) (S_0_0 : SyntheticSpectrum))
    (b : BiHom ((t' : ℤ)-s') ((t' : ℤ)-l) (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : Detects (background.convergence .sphere) (s,t,(t : ℤ)-k) (background.comparison.sphereE2 s t k x) a)
    (hb : Detects (background.convergence (.quotient q .sphere)) (s',t',(t' : ℤ)-l)
      ((background.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        (s',t',(t' : ℤ)-l) (background.comparison.sphereE2 s' t' l y)) b) :
    Detects (background.convergence (.quotient q .sphere))
      ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
      ((background.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
        (background.comparison.sphereE2 (s+s') (t+t') (k+l)
          (by simpa only [Nat.cast_add, Prod.mk_add_mk] using
            background.sphereAlgebra.product (s,t) (s',t') x y)))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b)) := by
  exact finite_action_complete q hq s t s' t' k l x y a b ha hb

end

open KIP126.Classical.Adams KIP126.Core.SpectralSequence in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Product detection on the actual homotopy groups and the same classical
sphere E₂ page. -/
public theorem classical_product_detection (s t s' t' : ℕ)
    (x : background.classical.sphere.Page 2 (s,t))
    (y : background.classical.sphere.Page 2 (s',t'))
    (a : HomotopyGroup (C := Spectrum) ((t : ℤ)-s) SphereSpectrum)
    (b : HomotopyGroup (C := Spectrum) ((t' : ℤ)-s') SphereSpectrum)
    (ha : ClassicalDetects (background.classicalConvergence .sphere) (s,t) x a)
    (hb : ClassicalDetects (background.classicalConvergence .sphere) (s',t') y b) :
    ClassicalDetects (background.classicalConvergence .sphere) ((s+s' : ℕ),(t+t' : ℕ))
      ((eqToHom (congrArg (background.classical.sphere.Page 2)
        (show ((s : ℤ),(t : ℤ)) + ((s' : ℤ),(t' : ℤ)) = (((s+s' : ℕ) : ℤ),((t+t' : ℕ) : ℤ)) by
          simp only [Prod.mk_add_mk,Nat.cast_add])))
        (background.sphereAlgebra.product (s,t) (s',t') x y))
      (eqToHom (congrArg (fun n : ℤ => Sphere (C := Spectrum) n)
        (by simp only [Nat.cast_add]; omega : ((t+t' : ℕ) : ℤ)-(s+s') =
          ((t : ℤ)-s)+((t' : ℤ)-s'))) ≫ classicalSphereProduct a b) := by
  let S : MappingObject (fun X : Spectrum => X=SphereSpectrum) := ⟨SphereSpectrum,rfl⟩
  let e := sphereMappingIso closedTensor
  let E := sphereMappingAdamsIso closedTensor background.classical
  let xm := E.inv.pageMap 2 (s,t) x
  let ym := E.inv.pageMap 2 (s',t') y
  let am := a ≫ e.inv
  let bm := b ≫ e.inv
  have ham : ClassicalDetects (mapping.convergence S.val S.val S.property S.property) (s,t) xm am :=
    product_classical_detects_map background.classicalTower e.inv
      (background.classicalConvergence .sphere) (mapping.convergence S.val S.val S.property S.property)
      (s,t) x a ha
  have hbm : ClassicalDetects (mapping.convergence S.val S.val S.property S.property) (s',t') ym bm :=
    product_classical_detects_map background.classicalTower e.inv
      (background.classicalConvergence .sphere) (mapping.convergence S.val S.val S.property S.property)
      (s',t') y b hb
  have hm := mappingComposition_detection_compatible S S S 2 (by decide) (s,t) (s',t') xm ym am bm
    ((product_mapping_detects_iff S S (s,t) xm am).mpr ham)
    ((product_mapping_detects_iff S S (s',t') ym bm).mpr hbm)
  have hd := (product_mapping_detects_iff S S _ _ _).mp hm
  have hout := product_classical_detects_map background.classicalTower e.hom
    (mapping.convergence S.val S.val S.property S.property) (background.classicalConvergence .sphere)
    (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))) _ _ hd
  have hx : E.hom.pageMap 2 (s,t) xm=x := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f => f.pageMap 2 ((s:ℤ),(t:ℤ))) E.inv_hom_id) x
    simpa only [SpectralSequenceMorphism.pageMap_comp, SpectralSequenceMorphism.pageMap_id,
      ModuleCat.comp_apply, ModuleCat.id_apply, xm] using h
  have hy : E.hom.pageMap 2 (s',t') ym=y := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f => f.pageMap 2 ((s':ℤ),(t':ℤ))) E.inv_hom_id) y
    simpa only [SpectralSequenceMorphism.pageMap_comp, SpectralSequenceMorphism.pageMap_id,
      ModuleCat.comp_apply, ModuleCat.id_apply, ym] using h
  have hp := KIP126.AdamsSynthetic.Completed.mapping_sphere_product (s,t) (s',t') xm ym
  change E.hom.pageMap 2 (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)))
      ((mappingComposition.pairing S S S).ssPairing.pair 2 (s,t) (s',t') xm ym) =
        background.sphereAlgebra.product (s,t) (s',t')
          (E.hom.pageMap 2 (s,t) xm) (E.hom.pageMap 2 (s',t') ym) at hp
  rw [hx,hy] at hp
  have hc : Moss.abutmentComposition S S S (s,t) (s',t') am bm ≫ e.hom =
      eqToHom (congrArg (Sphere (C := Spectrum))
        (show Moss.stem (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))) = Moss.stem (s,t)+Moss.stem (s',t') by
          dsimp [Moss.stem]; omega)) ≫ classicalSphereProduct a b := by
    have hh := product_mapping_composition_regrade ((t:ℤ)-s) ((t':ℤ)-s')
      (Moss.stem (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)))) (by dsimp [Moss.stem]; omega) am bm
    dsimp only [Moss.stem] at hh
    dsimp only [Moss.abutmentComposition, Moss.shiftMap, Moss.abutmentMap, Moss.stem, S]
    simpa only [am,bm,e,Category.assoc,Iso.inv_hom_id,Category.comp_id] using hh
  change ClassicalDetects (background.classicalConvergence .sphere) (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)))
    (E.hom.pageMap 2 _ ((mappingComposition.pairing S S S).ssPairing.pair 2 (s,t) (s',t') xm ym))
    (Moss.abutmentComposition S S S (s,t) (s',t') am bm ≫ e.hom) at hout
  rw [hp,hc] at hout
  have hdeg : ((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)) =
      (((s+s':ℕ):ℤ),((t+t':ℕ):ℤ)) := by simp only [Prod.mk_add_mk,Nat.cast_add]
  have hf := product_classical_detects_regrade (background.classicalConvergence .sphere) hdeg _ _ hout
  simp only [eqToHom_trans_assoc] at hf
  convert hf using 1
  rfl


end KIP126.Literature.Standard
