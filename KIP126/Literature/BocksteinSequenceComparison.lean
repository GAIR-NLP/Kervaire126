module

import all KIP126.Literature.BocksteinComparison
import KIP126.SpectralSequence.Basic.Category.Data
import KIP126.SpectralSequence.Basic.Proofs

/-! Generic comparison using the selected step-triangle isomorphisms of BocksteinComparison. -/

@[expose] section
namespace KIP126.Literature.BocksteinComparison.Sequence
open KIP126.AdamsSynthetic
open KIP126.Literature.BocksteinComparison.Stages
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v i
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X Y : C}

private def dataMorphismOfFinite
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type i} [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) (φ : ∀ i, (D i).V ⟶ (D' i).V)
    (hZ : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).Z n) ⟶
        Subobject.underlying.obj ((D' i).Z n)),
      lift ≫ ((D' i).Z n).arrow = ((D i).Z n).arrow ≫ φ i)
    (hB : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).B n) ⟶
        Subobject.underlying.obj ((D' i).B n)),
      lift ≫ ((D' i).B n).arrow = ((D i).B n).arrow ≫ φ i) :
    SSDataMorphism ι D D' where
  φ := φ
  preserves_Z i r := by
    cases r using WithTop.recTopCoe with
    | coe n => exact hZ i n
    | top =>
      let f := ((D i).Z ⊤).arrow ≫ φ i
      have hI : imageSubobject f ≤ (D' i).Z ⊤ := by
        apply (D' i).Z_top_greatest
        intro n
        apply imageSubobject_le f
          (Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top) ≫
            (hZ i n).choose)
        rw [Category.assoc, (hZ i n).choose_spec, ← Category.assoc,
          Subobject.ofLE_arrow]
      refine ⟨factorThruImageSubobject f ≫
        Subobject.ofLE (imageSubobject f) ((D' i).Z ⊤) hI, ?_⟩
      rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  preserves_B i r := by
    cases r using WithTop.recTopCoe with
    | coe n => exact hB i n
    | top =>
      let Q := (Subobject.pullback (φ i)).obj ((D' i).B ⊤)
      have hQ : (D i).B ⊤ ≤ Q := by
        apply (D i).B_top_least
        intro n
        apply Subobject.le_of_factors
        apply (pullback_factors_iff (φ i) ((D' i).B ⊤) (((D i).B n).arrow)).mpr
        rw [Subobject.factors_iff]
        have hn : (D' i).B n ≤ (D' i).B ⊤ := (D' i).B_mono le_top
        refine ⟨(hB i n).choose ≫
          Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn, ?_⟩
        calc
          ((hB i n).choose ≫ Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn) ≫
              ((D' i).B ⊤).arrow =
            (hB i n).choose ≫
              (Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn ≫ ((D' i).B ⊤).arrow) :=
            Category.assoc _ _ _
          _ = (hB i n).choose ≫ ((D' i).B n).arrow :=
            congrArg (fun q => (hB i n).choose ≫ q) (Subobject.ofLE_arrow hn)
          _ = ((D i).B n).arrow ≫ φ i := (hB i n).choose_spec
      refine ⟨Subobject.ofLE ((D i).B ⊤) Q hQ ≫
        Subobject.pullbackπ (φ i) ((D' i).B ⊤), ?_⟩
      rw [Category.assoc, (Subobject.isPullback (φ i) ((D' i).B ⊤)).w,
        ← Category.assoc, Subobject.ofLE_arrow]


private noncomputable def subobjectLift {R : Type} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] {N : ModuleCat.{v} R} (S : Subobject N)
    (f : M →ₗ[R] N) (hf : ∀ x, f x ∈ (ModuleCat.subobjectModule N) S) :
    M →ₗ[R] (Subobject.underlying.obj S : ModuleCat R) :=
  (LinearEquiv.ofInjective S.arrow.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)).symm.toLinearMap.comp
      (f.codRestrict _ hf)

private theorem subobjectLift_arrow {R : Type} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] {N : ModuleCat.{v} R} (S : Subobject N)
    (f : M →ₗ[R] N) (hf : ∀ x, f x ∈ (ModuleCat.subobjectModule N) S) (x : M) :
    S.arrow (subobjectLift S f hf x) = f x := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective S.arrow.hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)).apply_symm_apply
      ⟨f x, hf x⟩)

private theorem subobjectMorphism_exists {M N : ModuleCat.{v} ℤ}
    (A : Subobject M) (B : Subobject N) (g : M ⟶ N)
    (hg : ∀ a ∈ ModuleCat.subobjectModule M A, g a ∈ ModuleCat.subobjectModule N B) :
    ∃ lift : Subobject.underlying.obj A ⟶ Subobject.underlying.obj B,
      lift ≫ B.arrow = A.arrow ≫ g := by
  let f := g.hom.comp A.arrow.hom
  have hf : ∀ x, f x ∈ ModuleCat.subobjectModule N B :=
    fun x => hg _ (LinearMap.mem_range_self _ x)
  refine ⟨ModuleCat.ofHom (subobjectLift B f hf),?_⟩
  ext x
  exact subobjectLift_arrow B f hf x


private def firstPageEquiv (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (p : ℤ × ℤ) :
    T.FirstPage p ≃ₗ[ℤ] U.FirstPage p :=
  { toFun := firstPageTransport T U e p
    invFun := fun x => x ≫ (selectedLayerIso T U e p.1).inv
    left_inv := by intro x; simp [firstPageTransport, Category.assoc]
    right_inv := by intro x; simp [firstPageTransport, Category.assoc]
    map_add' := by intro x y; simp only [firstPageTransport, Preadditive.add_comp]
    map_smul' := by intro n x; simp only [firstPageTransport, Preadditive.zsmul_comp, RingHom.id_apply] }

private def stageEquiv (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n s : ℤ) :
    HomotopyGroup n (T.stageAt s) ≃ₗ[ℤ] HomotopyGroup n (U.stageAt s) :=
  { toFun := stageTransport T U e n s
    invFun := fun x => x ≫ (stageIso T U e s.toNat).inv
    left_inv := by intro x; simp [stageTransport, Category.assoc]
    right_inv := by intro x; simp [stageTransport, Category.assoc]
    map_add' := by intro x y; simp only [stageTransport, Preadditive.add_comp]
    map_smul' := by intro m x; simp only [stageTransport, Preadditive.zsmul_comp, RingHom.id_apply] }

private theorem firstPageEquiv_cycles_iff (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (r : ℕ) (hr : 1 ≤ r)
    (p : ℤ × ℤ) (x : T.FirstPage p) :
    firstPageEquiv T U e p x ∈ U.cycles r hr p ↔ x ∈ T.cycles r hr p := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨a, rfl⟩ := (stageEquiv T U e (p.2-p.1-1) (p.1+r)).surjective a
    refine ⟨a, ?_⟩
    apply (stageEquiv T U e (p.2-p.1-1) (p.1+1)).injective
    change stageTransport T U e _ _ (a ≫ T.mapAt _) =
      stageTransport T U e _ _ (T.connecting p x)
    rw [← selectedStageMap_natural, ← selectedConnecting_natural]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨stageTransport T U e (p.2-p.1-1) (p.1+r) a, ?_⟩
    change stageTransport T U e _ _ a ≫ U.mapAt _ =
      U.connecting p (firstPageTransport T U e p x)
    rw [selectedStageMap_natural, selectedConnecting_natural]
    exact congrArg (stageTransport T U e _ _) ha

private theorem firstPageEquiv_boundaries_iff (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (r : ℕ) (hr : 1 ≤ r)
    (p : ℤ × ℤ) (x : T.FirstPage p) :
    firstPageEquiv T U e p x ∈ U.boundaries r hr p ↔ x ∈ T.boundaries r hr p := by
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨a, rfl⟩ := (stageEquiv T U e (p.2-p.1) p.1).surjective a
    refine ⟨a, ?_, ?_⟩
    · apply (stageEquiv T U e (p.2-p.1) (p.1-r+1)).injective
      change stageTransport T U e _ _ (a ≫ T.mapAt _) =
        stageEquiv T U e _ _ 0
      rw [map_zero, ← selectedStageMap_natural]
      exact ha
    · apply (firstPageEquiv T U e p).injective
      change firstPageTransport T U e p (T.layerMap p a) = _
      rw [selectedLayerMap_natural]
      exact hx
  · rintro ⟨a, ha, hx⟩
    refine ⟨stageTransport T U e (p.2-p.1) p.1 a, ?_, ?_⟩
    · change stageTransport T U e _ _ a ≫ U.mapAt _ = 0
      rw [selectedStageMap_natural]
      change stageEquiv T U e _ _ (a ≫ T.mapAt _) = 0
      rw [show a ≫ T.mapAt _ = 0 from ha, map_zero]
    · rw [← selectedLayerMap_natural]
      exact congrArg (firstPageTransport T U e p) hx

private def cycleAmbientEquiv (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (p : ℤ × ℤ) :
    T.cycles 2 (by decide) p ≃ₗ[ℤ] U.cycles 2 (by decide) p where
  toFun x := ⟨firstPageEquiv T U e p x.val,
    (firstPageEquiv_cycles_iff T U e 2 (by decide) p x.val).mpr x.property⟩
  invFun y := ⟨(firstPageEquiv T U e p).symm y.val, by
    apply (firstPageEquiv_cycles_iff T U e 2 (by decide) p _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((firstPageEquiv T U e p).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((firstPageEquiv T U e p).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((firstPageEquiv T U e p).map_add x.val y.val)
  map_smul' n x := Subtype.ext ((firstPageEquiv T U e p).map_smul n x.val)

section Presented
variable {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
  {D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
  {d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}
  {d' : ∀ (r : ℤ) (p : ℤ × ℤ), (E p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (E (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}
  (P : TowerSequencePresentation unit T D d) (Q : TowerSequencePresentation unit U E d')
  (e : X ≅ Y)

private def presentedAmbientIso (p : ℤ × ℤ) : (D p).V ≅ (E p).V :=
  P.ambient p ≪≫ (cycleAmbientEquiv T U e p).toModuleIso ≪≫ (Q.ambient p).symm

private theorem presentedAmbientIso_value (p : ℤ × ℤ) (x : (D p).V) :
    ((Q.ambient p).hom ((presentedAmbientIso P Q e p).hom x)).val =
      firstPageTransport T U e p (((P.ambient p).hom x).val) := by
  change ((Q.ambient p).hom ((Q.ambient p).inv
    (cycleAmbientEquiv T U e p ((P.ambient p).hom x)))).val = _
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

private theorem presentedAmbientIso_cycles (p : ℤ × ℤ) (n : ℕ) (x : (D p).V) :
    (presentedAmbientIso P Q e p).hom x ∈ ModuleCat.subobjectModule _ ((E p).Z n) ↔
      x ∈ ModuleCat.subobjectModule _ ((D p).Z n) := by
  rw [P.cycles, Q.cycles, presentedAmbientIso_value]
  exact firstPageEquiv_cycles_iff T U e (n+2) (by omega) p _

private theorem presentedAmbientIso_boundaries (p : ℤ × ℤ) (n : ℕ) (x : (D p).V) :
    (presentedAmbientIso P Q e p).hom x ∈ ModuleCat.subobjectModule _ ((E p).B n) ↔
      x ∈ ModuleCat.subobjectModule _ ((D p).B n) := by
  rw [P.boundaries, Q.boundaries, presentedAmbientIso_value]
  exact firstPageEquiv_boundaries_iff T U e (n+2) (by omega) p _

private def presentedDataMap : SSDataMorphism (ℤ × ℤ) D E :=
  dataMorphismOfFinite D E (fun p => (presentedAmbientIso P Q e p).hom)
    (fun p n => subobjectMorphism_exists _ _ _ (fun x hx =>
      (presentedAmbientIso_cycles P Q e p n x).mpr hx))
    (fun p n => subobjectMorphism_exists _ _ _ (fun x hx =>
      (presentedAmbientIso_boundaries P Q e p n x).mpr hx))

private def presentedDataInverse : SSDataMorphism (ℤ × ℤ) E D :=
  dataMorphismOfFinite E D (fun p => (presentedAmbientIso P Q e p).inv)
    (fun p n => subobjectMorphism_exists _ _ _ (fun x hx => by
      apply (presentedAmbientIso_cycles P Q e p n _).mp
      rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
      exact hx))
    (fun p n => subobjectMorphism_exists _ _ _ (fun x hx => by
      apply (presentedAmbientIso_boundaries P Q e p n _).mp
      rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
      exact hx))

private theorem presentedDataMap_inverse :
    (presentedDataMap P Q e).comp (presentedDataInverse P Q e) = SSDataMorphism.id D := by
  apply SSDataMorphism.ext
  funext p
  exact (presentedAmbientIso P Q e p).hom_inv_id

private theorem presentedDataInverse_map :
    (presentedDataInverse P Q e).comp (presentedDataMap P Q e) = SSDataMorphism.id E := by
  apply SSDataMorphism.ext
  funext p
  exact (presentedAmbientIso P Q e p).inv_hom_id

/-- Finite and infinity pages use the quotient maps of this same ambient map. -/
private def presentedPageIso (p : ℤ × ℤ) (r : WithTop ℕ) :
    (D p).page r ≅ (E p).page r where
  hom := (presentedDataMap P Q e).pageMap p r
  inv := (presentedDataInverse P Q e).pageMap p r
  hom_inv_id := by
    rw [← SSDataMorphism.pageMap_comp, presentedDataMap_inverse, SSDataMorphism.pageMap_id]
  inv_hom_id := by
    rw [← SSDataMorphism.pageMap_comp, presentedDataInverse_map, SSDataMorphism.pageMap_id]

private theorem presentedDataMap_cycle_value (p : ℤ × ℤ) (n : WithTop ℕ)
    (z : (Subobject.underlying.obj ((D p).Z n) : ModuleCat ℤ)) :
    ((Q.ambient p).hom (((E p).Z n).arrow ((presentedDataMap P Q e).cycleMap p n z))).val =
      firstPageTransport T U e p (((P.ambient p).hom (((D p).Z n).arrow z)).val) := by
  have h := ConcreteCategory.congr_hom ((presentedDataMap P Q e).cycleMap_arrow p n) z
  change ((E p).Z n).arrow ((presentedDataMap P Q e).cycleMap p n z) =
    (presentedAmbientIso P Q e p).hom (((D p).Z n).arrow z) at h
  rw [h, presentedAmbientIso_value]

private theorem dataMap_page_value {D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    (F : SSDataMorphism (ℤ × ℤ) D E) (p : ℤ × ℤ) (n : WithTop ℕ)
    (z : (Subobject.underlying.obj ((D p).Z n) : ModuleCat ℤ)) :
    F.pageMap p n ((D p).pageπ n z) = (E p).pageπ n (F.cycleMap p n z) :=
  ConcreteCategory.congr_hom (F.pageπ_pageMap p n) z

omit Q e in
private theorem presented_lift_exists (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((D p).Z (↑(r-2).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    ∃ a : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)),
      T.connecting p (((P.ambient p).hom (((D p).Z _).arrow z)).val) =
        a ≫ T.mapAt (show p.1+1 ≤ p.1+r by omega) := by
  have hZ : ((D p).Z (↑(r-2).toNat : WithTop ℕ)).arrow z ∈
      ModuleCat.subobjectModule _ ((D p).Z (↑(r-2).toNat : WithTop ℕ)) :=
    LinearMap.mem_range_self _ z
  have hz := (P.cycles p (r-2).toNat _).mp hZ
  have range_eq (m s t t' : ℤ) (hst : s ≤ t) (h : t = t') :
      LinearMap.range (inducedMap (T.mapAt hst) m).toIntLinearMap =
        LinearMap.range (inducedMap (T.mapAt (show s ≤ t' by omega)) m).toIntLinearMap := by
    subst t'
    rfl
  change T.connecting p (((P.ambient p).hom (((D p).Z _).arrow z)).val) ∈
    LinearMap.range (inducedMap (T.mapAt (show p.1+1 ≤ p.1+((r-2).toNat+2:ℕ) by omega))
      (p.2-p.1-1)).toIntLinearMap at hz
  rw [range_eq _ _ _ (p.1+r) _ (by omega)] at hz
  obtain ⟨a, ha⟩ := hz
  exact ⟨a, ha.symm⟩

omit Q e in
private theorem presented_layer_cycle_exists (r : ℤ) (_hr : 2 ≤ r) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    ∃ z : (Subobject.underlying.obj ((D p).Z (↑(r-2).toNat : WithTop ℕ)) : ModuleCat ℤ),
      (((P.ambient p).hom (((D p).Z _).arrow z)).val) = T.layerMap p a := by
  have hzero : T.connecting p (T.layerMap p a) = 0 := by
    let f := T.mapAt (show p.1 ≤ p.1+1 by omega)
    have h : HasFunctorialCofiber.cofibι f ≫ HasFunctorialCofiber.cofibδ f = 0 :=
      comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished f)
    change AbstractAdamsTower.desuspend _ _
      ((a ≫ HasFunctorialCofiber.cofibι f) ≫ HasFunctorialCofiber.cofibδ f) = 0
    rw [Category.assoc, h, comp_zero, map_zero]
  have hcyc (n : ℕ) (hn : 1 ≤ n) : T.layerMap p a ∈ T.cycles n hn p := by
    change T.connecting p (T.layerMap p a) ∈ LinearMap.range _
    rw [hzero]
    exact Submodule.zero_mem _
  let x : T.cycles 2 (by decide) p := ⟨T.layerMap p a, hcyc 2 (by decide)⟩
  have hx : (P.ambient p).inv x ∈ ModuleCat.subobjectModule _
      ((D p).Z (↑(r-2).toNat : WithTop ℕ)) := by
    apply (P.cycles p (r-2).toNat _).mpr
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
    exact hcyc _ (by omega)
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, ?_⟩
  rw [show ((D p).Z _).arrow z = (P.ambient p).inv x from hz,
    ← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

/-- Differential compatibility through a lifted representative and the
step-triangle comparison, with labels induced by the ambient map. -/
private theorem presentedPageIso_differential (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (presentedPageIso P Q e p (↑(r-2).toNat : WithTop ℕ)).hom ≫ d' r p =
      d r p ≫ (presentedPageIso P Q e (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ)).hom := by
  let n := (r-2).toNat
  let F := presentedDataMap P Q e
  letI : Epi ((D p).pageπ (↑n : WithTop ℕ)) := by
    dsimp only [SSData.pageπ]; infer_instance
  apply (cancel_epi ((D p).pageπ (↑n : WithTop ℕ))).mp
  ext z
  change d' r p (F.pageMap p n ((D p).pageπ n z)) =
    F.pageMap (p+(r,r-1)) n (d r p ((D p).pageπ n z))
  obtain ⟨a, ha⟩ := presented_lift_exists P r hr p z
  let a' : HomotopyGroup ((p+(r,r-1)).2-(p+(r,r-1)).1) (T.stageAt (p.1+r)) :=
    Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1+r)))
      (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)) a
  obtain ⟨z', hz'⟩ := presented_layer_cycle_exists P r hr (p+(r,r-1)) a'
  have h := presentedDifferential_transport T U e D E d d' P Q r hr p z a z'
    (F.cycleMap p n z) (F.cycleMap (p+(r,r-1)) n z')
    (presentedDataMap_cycle_value P Q e p n z)
    (presentedDataMap_cycle_value P Q e (p+(r,r-1)) n z') ha hz'
  rw [dataMap_page_value F, h.2, h.1, dataMap_page_value F]

private theorem presentedPageIso_inverse_differential (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (presentedPageIso P Q e p (↑(r-2).toNat : WithTop ℕ)).inv ≫ d r p =
      d' r p ≫ (presentedPageIso P Q e (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ)).inv := by
  apply (cancel_mono (presentedPageIso P Q e (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← presentedPageIso_differential P Q e r hr p]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]


/-- The same comparison restricts to the actual cycle subobjects, including ∞. -/
private def presentedCycleIso (p : ℤ × ℤ) (r : WithTop ℕ) :
    Subobject.underlying.obj ((D p).Z r) ≅ Subobject.underlying.obj ((E p).Z r) where
  hom := (presentedDataMap P Q e).cycleMap p r
  inv := (presentedDataInverse P Q e).cycleMap p r
  hom_inv_id := by
    rw [← SSDataMorphism.cycleMap_comp, presentedDataMap_inverse, SSDataMorphism.cycleMap_id]
  inv_hom_id := by
    rw [← SSDataMorphism.cycleMap_comp, presentedDataInverse_map, SSDataMorphism.cycleMap_id]

/-- Boundary maps are determined uniquely by their ambient square. -/
private def dataBoundaryMap {D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    (F : SSDataMorphism (ℤ × ℤ) D E) (p : ℤ × ℤ) (r : WithTop ℕ) :
    Subobject.underlying.obj ((D p).B r) ⟶ Subobject.underlying.obj ((E p).B r) :=
  (F.preserves_B p r).choose

private theorem dataBoundaryMap_arrow {D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    (F : SSDataMorphism (ℤ × ℤ) D E) (p : ℤ × ℤ) (r : WithTop ℕ) :
    dataBoundaryMap F p r ≫ ((E p).B r).arrow = ((D p).B r).arrow ≫ F.φ p :=
  (F.preserves_B p r).choose_spec

/-- The same comparison restricts to the actual boundary subobjects, including ∞. -/
private def presentedBoundaryIso (p : ℤ × ℤ) (r : WithTop ℕ) :
    Subobject.underlying.obj ((D p).B r) ≅ Subobject.underlying.obj ((E p).B r) where
  hom := dataBoundaryMap (presentedDataMap P Q e) p r
  inv := dataBoundaryMap (presentedDataInverse P Q e) p r
  hom_inv_id := by
    apply (cancel_mono ((D p).B r).arrow).mp
    rw [Category.assoc, dataBoundaryMap_arrow, ← Category.assoc, dataBoundaryMap_arrow]
    change (((D p).B r).arrow ≫ (presentedAmbientIso P Q e p).hom) ≫
      (presentedAmbientIso P Q e p).inv = 𝟙 _ ≫ ((D p).B r).arrow
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono ((E p).B r).arrow).mp
    rw [Category.assoc, dataBoundaryMap_arrow, ← Category.assoc, dataBoundaryMap_arrow]
    change (((E p).B r).arrow ≫ (presentedAmbientIso P Q e p).inv) ≫
      (presentedAmbientIso P Q e p).hom = 𝟙 _ ≫ ((E p).B r).arrow
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The page comparison is the quotient of the very same cycle comparison. -/
private theorem presentedPageIso_quotient (p : ℤ × ℤ) (r : WithTop ℕ) :
    (D p).pageπ r ≫ (presentedPageIso P Q e p r).hom =
      (presentedCycleIso P Q e p r).hom ≫ (E p).pageπ r :=
  (presentedDataMap P Q e).pageπ_pageMap p r

/-- The cycle comparison commutes with every inclusion Z_s ⟶ Z_r. -/
private theorem presentedCycleIso_inclusion (p : ℤ × ℤ) (r s : WithTop ℕ) (hrs : r ≤ s) :
    Subobject.ofLE ((D p).Z s) ((D p).Z r) ((D p).Z_anti hrs) ≫
      (presentedCycleIso P Q e p r).hom =
    (presentedCycleIso P Q e p s).hom ≫
      Subobject.ofLE ((E p).Z s) ((E p).Z r) ((E p).Z_anti hrs) :=
  (presentedDataMap P Q e).cycleMap_ofLE p hrs


end Presented

/-- Canonical page-two presentation of an Adams-indexed sequence, with its
unconstrained pre-initial differential entries filled by zero. The underlying
SSData, all valid pages, and every valid differential are unchanged. -/
private def normalizedAdamsSequence
    (S : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1)) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  r₀ := 2
  ssData := S.ssData
  diffDeg r := (r,r-1)
  d r p := if 2 ≤ r then normalizedDifferential S h0 hd r p else 0
  d_comp_d r p := by
    by_cases hr : 2 ≤ r
    · repeat rw [if_pos hr]
      rcases S with ⟨⟨r₀, D, δ, d⟩, hdd, hZ, hB⟩
      change r₀ = 2 at h0
      subst r₀
      have hδ : δ = fun r => (r,r-1) := funext hd
      subst δ
      unfold normalizedDifferential
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id]
        using hdd r p
    · repeat rw [if_neg hr]
      exact zero_comp
  Z_succ r p hr := by
    repeat rw [if_pos hr]
    rcases S with ⟨⟨r₀, D, δ, d⟩, hdd, hZ, hB⟩
    change r₀ = 2 at h0
    subst r₀
    have hδ : δ = fun r => (r,r-1) := funext hd
    subst δ
    unfold normalizedDifferential
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id]
      using hZ r p hr
  B_succ r p hr := by
    repeat rw [if_pos hr]
    rcases S with ⟨⟨r₀, D, δ, d⟩, hdd, hZ, hB⟩
    change r₀ = 2 at h0
    subst r₀
    have hδ : δ = fun r => (r,r-1) := funext hd
    subst δ
    unfold normalizedDifferential
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id]
      using hB r p hr

private theorem normalizedAdamsSequence_d
    (S : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (normalizedAdamsSequence S h0 hd).d r p = normalizedDifferential S h0 hd r p := by
  exact if_pos hr

section SequenceIso
variable {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
  (S S' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
  (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1))
  (h0' : S'.r₀ = 2) (hd' : ∀ r, S'.diffDeg r = (r,r-1))
  (P : TowerSequencePresentation unit T S.ssData (normalizedDifferential S h0 hd))
  (Q : TowerSequencePresentation unit U S'.ssData (normalizedDifferential S' h0' hd'))
  (e : X ≅ Y)

/-- The forward full-record morphism after filling only pre-initial entries by zero. -/
private def presentedSequenceMap : SpectralSequenceMorphism
    (normalizedAdamsSequence S h0 hd) (normalizedAdamsSequence S' h0' hd') where
  φ := (presentedDataMap P Q e).φ
  preserves_Z := (presentedDataMap P Q e).preserves_Z
  preserves_B := (presentedDataMap P Q e).preserves_B
  r₀_eq := rfl
  diffDeg_eq := rfl
  comm_d r p := by
    change (presentedDataMap P Q e).pageMap p (↑(r-2).toNat : WithTop ℕ) ≫
        (if 2 ≤ r then normalizedDifferential S' h0' hd' r p else 0) =
      (if 2 ≤ r then normalizedDifferential S h0 hd r p else 0) ≫
        (presentedDataMap P Q e).pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) ≫ 𝟙 _
    rw [Category.comp_id]
    by_cases hr : 2 ≤ r
    · repeat rw [if_pos hr]
      exact presentedPageIso_differential P Q e r hr p
    · repeat rw [if_neg hr]
      simp only [comp_zero, zero_comp]

private def presentedSequenceInverse : SpectralSequenceMorphism
    (normalizedAdamsSequence S' h0' hd') (normalizedAdamsSequence S h0 hd) where
  φ := (presentedDataInverse P Q e).φ
  preserves_Z := (presentedDataInverse P Q e).preserves_Z
  preserves_B := (presentedDataInverse P Q e).preserves_B
  r₀_eq := rfl
  diffDeg_eq := rfl
  comm_d r p := by
    change (presentedDataInverse P Q e).pageMap p (↑(r-2).toNat : WithTop ℕ) ≫
        (if 2 ≤ r then normalizedDifferential S h0 hd r p else 0) =
      (if 2 ≤ r then normalizedDifferential S' h0' hd' r p else 0) ≫
        (presentedDataInverse P Q e).pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) ≫ 𝟙 _
    rw [Category.comp_id]
    by_cases hr : 2 ≤ r
    · repeat rw [if_pos hr]
      exact presentedPageIso_inverse_differential P Q e r hr p
    · repeat rw [if_neg hr]
      simp only [comp_zero, zero_comp]

/-- Categorical isomorphism of normalized spectral sequences induced
by an ambient isomorphism. -/
private def presentedSequenceIso :
    normalizedAdamsSequence S h0 hd ≅ normalizedAdamsSequence S' h0' hd' where
  hom := presentedSequenceMap S S' h0 hd h0' hd' P Q e
  inv := presentedSequenceInverse S S' h0 hd h0' hd' P Q e
  hom_inv_id := by
    apply SpectralSequenceMorphism.ext
    funext p
    exact (presentedAmbientIso P Q e p).hom_inv_id
  inv_hom_id := by
    apply SpectralSequenceMorphism.ext
    funext p
    exact (presentedAmbientIso P Q e p).inv_hom_id

end SequenceIso

end
end KIP126.Literature.BocksteinComparison.Sequence
end
