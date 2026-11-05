module

public import KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.AdamsNaturality
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.AdamsSequence
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.AdamsTower
import KIP126.AdamsSynthetic.Coherence

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.Source
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence KIP126.Synthetic.Context
universe u v i
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X Y : C}

private theorem cofiberMap_isIso {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ g=f ≫ b) [IsIso a] [IsIso b] :
    IsIso (HasFunctorialCofiber.cofibMap f g a b h) := by
  let φ : Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f) ⟶
      Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g) :=
    { hom₁ := a
      hom₂ := b
      hom₃ := HasFunctorialCofiber.cofibMap f g a b h
      comm₁ := h.symm
      comm₂ := (HasFunctorialCofiber.cofibMap_ι f g a b h).symm
      comm₃ := (HasFunctorialCofiber.cofibMap_δ f g a b h).symm }
  exact isIso₃_of_isIso₁₂ φ (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g) inferInstance inferInstance

private theorem towerLayerMap_isIso {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (s : ℤ) : IsIso (φ.layer s) := by
  letI := hi (s+1).toNat
  letI := hi s.toNat
  exact cofiberMap_isIso _ _ _ _ _


private theorem towerHomMap_bijective {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (m s : ℤ) : Function.Bijective (towerHomMap φ m s) := by
  letI := hi s.toNat
  constructor
  · intro a b h
    exact (cancel_mono (φ.stage s.toNat)).mp h
  · intro b
    refine ⟨b ≫ inv (φ.stage s.toNat),?_⟩
    change (b ≫ inv (φ.stage s.toNat)) ≫ φ.stage s.toNat=b
    simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]

private theorem towerE1Map_bijective {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) : Function.Bijective (towerE1Map φ p) := by
  letI := towerLayerMap_isIso φ hi p.1
  constructor
  · intro a b h
    exact (cancel_mono (φ.layer p.1)).mp h
  · intro b
    refine ⟨b ≫ inv (φ.layer p.1),?_⟩
    change (b ≫ inv (φ.layer p.1)) ≫ φ.layer p.1=b
    simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]

private theorem towerE1Map_cycles_iff {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (r : ℕ) (hr : 1 ≤ r) (p : ℤ×ℤ)
    (a : T.FirstPage p) : towerE1Map φ p a ∈ U.cycles r hr p ↔ a ∈ T.cycles r hr p := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨b',rfl⟩ := (towerHomMap_bijective φ hi (p.2-p.1-1) (p.1+r)).2 b
    refine ⟨b',?_⟩
    apply (towerHomMap_bijective φ hi (p.2-p.1-1) (p.1+1)).1
    change towerHomMap φ _ _ (towerI T _ _ _ _ b') = _
    rw [← towerI_natural,← towerK_natural]
    exact hb
  · exact towerE1Map_cycles φ r hr p

private theorem towerE1Map_boundaries_iff {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (r : ℕ) (hr : 1 ≤ r) (p : ℤ×ℤ)
    (a : T.FirstPage p) : towerE1Map φ p a ∈ U.boundaries r hr p ↔ a ∈ T.boundaries r hr p := by
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨b',rfl⟩ := (towerHomMap_bijective φ hi (p.2-p.1) p.1).2 b
    refine ⟨b',?_,?_⟩
    · apply (towerHomMap_bijective φ hi (p.2-p.1) (p.1-r+1)).1
      change towerHomMap φ _ _ (towerI T _ _ _ _ b') = _
      rw [map_zero,← towerI_natural]
      exact hb
    · apply (towerE1Map_bijective φ hi p).1
      rw [towerJ_natural]
      exact hba
  · exact towerE1Map_boundaries φ r hr p

private theorem towerCycleMap_bijective {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) : Function.Bijective (towerCycleMap φ p) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact (towerE1Map_bijective φ hi p).1 (congrArg Subtype.val h)
  · intro b
    obtain ⟨a,ha⟩ := (towerE1Map_bijective φ hi p).2 b.val
    have hac : a ∈ T.cycles 2 (by decide) p :=
      (towerE1Map_cycles_iff φ hi 2 (by decide) p a).mp (ha ▸ b.property)
    exact ⟨⟨a,hac⟩,Subtype.ext ha⟩


private def towerAmbientEquiv {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) : cycleAmbient T p ≃ₗ[ℤ] cycleAmbient U p :=
  LinearEquiv.ofBijective (towerCycleMap φ p) (towerCycleMap_bijective φ hi p)

private theorem towerAmbientEquiv_symm_cycles {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) (n : ℕ) (a : cycleAmbient U p)
    (ha : a ∈ finiteCycles U p n) :
    (towerAmbientEquiv φ hi p).symm a ∈ finiteCycles T p n := by
  have he : towerCycleMap φ p ((towerAmbientEquiv φ hi p).symm a)=a :=
    (towerAmbientEquiv φ hi p).apply_symm_apply a
  apply (towerE1Map_cycles_iff φ hi (n+2) (by omega) p _).mp
  change (towerCycleMap φ p ((towerAmbientEquiv φ hi p).symm a)).val ∈ _
  rw [he]
  exact ha

private theorem towerAmbientEquiv_symm_boundaries {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) (n : ℕ) (a : cycleAmbient U p)
    (ha : a ∈ finiteBoundaries U p n) :
    (towerAmbientEquiv φ hi p).symm a ∈ finiteBoundaries T p n := by
  have he : towerCycleMap φ p ((towerAmbientEquiv φ hi p).symm a)=a :=
    (towerAmbientEquiv φ hi p).apply_symm_apply a
  apply (towerE1Map_boundaries_iff φ hi (n+2) (by omega) p _).mp
  change (towerCycleMap φ p ((towerAmbientEquiv φ hi p).symm a)).val ∈ _
  rw [he]
  exact ha

private theorem towerAmbientEquiv_symm_allCycles {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) (r : WithTop ℕ) (a : cycleAmbient U p)
    (ha : a ∈ allCycles U p r) :
    (towerAmbientEquiv φ hi p).symm a ∈ allCycles T p r := by
  cases r using WithTop.recTopCoe with
  | top =>
    simp only [allCycles,Submodule.mem_iInf] at ha ⊢
    exact fun n => towerAmbientEquiv_symm_cycles φ hi p n a (ha n)
  | coe n => exact towerAmbientEquiv_symm_cycles φ hi p n a ha

private theorem towerAmbientEquiv_symm_allBoundaries {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) (r : WithTop ℕ) (a : cycleAmbient U p)
    (ha : a ∈ allBoundaries U p r) :
    (towerAmbientEquiv φ hi p).symm a ∈ allBoundaries T p r := by
  cases r using WithTop.recTopCoe with
  | top =>
    have hmap : (allBoundaries U p ⊤).map (towerAmbientEquiv φ hi p).symm.toLinearMap ≤
        allBoundaries T p ⊤ := by
      simp only [allBoundaries,Submodule.map_iSup]
      refine iSup_le fun n => le_trans ?_ (le_iSup (finiteBoundaries T p) n)
      rintro _ ⟨b,hb,rfl⟩
      exact towerAmbientEquiv_symm_boundaries φ hi p n b hb
    exact hmap ⟨a,ha,rfl⟩
  | coe n => exact towerAmbientEquiv_symm_boundaries φ hi p n a ha

private def towerSSDataInverse {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) : SSDataMorphism (ℤ×ℤ) (towerSSData U) (towerSSData T) where
  φ p := ModuleCat.ofHom (towerAmbientEquiv φ hi p).symm.toLinearMap
  preserves_Z p r := towerSubmoduleLift_exists _ _ _
    (fun a ha => towerAmbientEquiv_symm_allCycles φ hi p r a ha)
  preserves_B p r := towerSubmoduleLift_exists _ _ _
    (fun a ha => towerAmbientEquiv_symm_allBoundaries φ hi p r a ha)

private def towerPageIso {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} {f : X ⟶ Y} (φ : TowerMap unit T U f)
    (hi : ∀ n, IsIso (φ.stage n)) (p : ℤ×ℤ) (r : WithTop ℕ) :
    (towerSSData T p).page r ≅ (towerSSData U p).page r where
  hom := (towerSSDataMap φ).pageMap p r
  inv := (towerSSDataInverse φ hi).pageMap p r
  hom_inv_id := by
    have hc : (towerSSDataMap φ).comp (towerSSDataInverse φ hi)=SSDataMorphism.id (towerSSData T) := by
      apply SSDataMorphism.ext
      funext q
      ext a
      exact (towerAmbientEquiv φ hi q).symm_apply_apply a
    rw [← SSDataMorphism.pageMap_comp,hc,SSDataMorphism.pageMap_id]
  inv_hom_id := by
    have hc : (towerSSDataInverse φ hi).comp (towerSSDataMap φ)=SSDataMorphism.id (towerSSData U) := by
      apply SSDataMorphism.ext
      funext q
      ext a
      exact (towerAmbientEquiv φ hi q).apply_symm_apply a
    rw [← SSDataMorphism.pageMap_comp,hc,SSDataMorphism.pageMap_id]

omit [HasFunctorialCofiber (C := C)] in
private def triangleIso₂₃ (T U : Triangle C)
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C)
    (e₂ : T.obj₂ ≅ U.obj₂) (e₃ : T.obj₃ ≅ U.obj₃)
    (h : T.mor₂ ≫ e₃.hom = e₂.hom ≫ U.mor₂) : T ≅ U :=
  (rotCompInvRot.app T) ≪≫ (invRotate C).mapIso
    (isoTriangleOfIso₁₂ T.rotate U.rotate (rot_of_distTriang _ hT)
      (rot_of_distTriang _ hU) e₂ e₃ h) ≪≫ (rotCompInvRot.app U).symm

omit [HasFunctorialCofiber (C := C)] in
private theorem triangleIso₂₃_hom₂ (T U : Triangle C)
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C)
    (e₂ : T.obj₂ ≅ U.obj₂) (e₃ : T.obj₃ ≅ U.obj₃)
    (h : T.mor₂ ≫ e₃.hom = e₂.hom ≫ U.mor₂) :
    (triangleIso₂₃ T U hT hU e₂ e₃ h).hom.hom₂ = e₂.hom := by
  simp [triangleIso₂₃]
  exact Category.comp_id _

private def towerNextIso {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} (n : ℕ) (e : T.stage n ≅ U.stage n) :
    {e' : T.stage (n+1) ≅ U.stage (n+1) //
      e'.hom ≫ U.map (Nat.le_succ n) = T.map (Nat.le_succ n) ≫ e.hom} := by
  let f := T.map (Nat.le_succ n)
  let g := U.map (Nat.le_succ n)
  let A := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  let B := Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g)
  let el : A.obj₃ ≅ B.obj₃ := (T.layerIso n) ≪≫
    whiskerLeftIso H e ≪≫ (U.layerIso n).symm
  have h : A.mor₂ ≫ el.hom = e.hom ≫ B.mor₂ := by
    change HasFunctorialCofiber.cofibι f ≫
      ((T.layerIso n).hom ≫ (H ◁ e.hom) ≫ (U.layerIso n).inv) =
      e.hom ≫ HasFunctorialCofiber.cofibι g
    rw [← Category.assoc,← Category.assoc,T.layer_unit]
    change (adamsUnit unit (T.stage n) ≫ H ◁ e.hom) ≫ (U.layerIso n).inv = _
    rw [← adamsUnit_naturality unit e.hom]
    dsimp only [adamsUnit]
    rw [Category.assoc,← U.layer_unit]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    rfl
  let et := triangleIso₂₃ A B (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g) e el h
  refine ⟨Triangle.π₁.mapIso et,?_⟩
  have hc := et.hom.comm₁
  rw [show et.hom.hom₂=e.hom from triangleIso₂₃_hom₂ _ _ _ _ _ _ _] at hc
  exact hc.symm

private def towerStageIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) : ∀ n, T.stage n ≅ U.stage n
  | 0 => T.zeroIso ≪≫ e ≪≫ U.zeroIso.symm
  | n+1 => (towerNextIso n (towerStageIso T U e n)).val

private theorem towerStageIso_natural_step (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (towerStageIso T U e (n+1)).hom ≫ U.map (Nat.le_succ n) =
      T.map (Nat.le_succ n) ≫ (towerStageIso T U e n).hom :=
  (towerNextIso n (towerStageIso T U e n)).property

private theorem towerStageIso_natural (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s t : ℕ) (h : s≤t) :
    (towerStageIso T U e t).hom ≫ U.map h =
      T.map h ≫ (towerStageIso T U e s).hom := by
  induction t,h using Nat.le_induction with
  | base => simp only [T.map_self,U.map_self,Category.comp_id,Category.id_comp]
  | succ t h ih =>
    rw [← U.map_comp h (Nat.le_succ t),← T.map_comp h (Nat.le_succ t)]
    rw [← Category.assoc,towerStageIso_natural_step,Category.assoc,ih,Category.assoc]

private def towerIsoMap (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) : TowerMap unit T U e.hom where
  stage n := (towerStageIso T U e n).hom
  natural {s t} h := towerStageIso_natural T U e s t h
  zero := by simp only [towerStageIso,Iso.trans_hom,Iso.symm_hom,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]

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


section PresentationComparison
variable {D : (ℤ×ℤ) → SSData (ModuleCat.{v} ℤ)}
  {T : AbstractAdamsTower unit X}
  {d : ∀ (r : ℤ) (p : ℤ×ℤ), (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}

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

private def presentationDataMap (P : TowerSequencePresentation unit T D d) :
    SSDataMorphism (ℤ×ℤ) D (towerSSData T) :=
  dataMorphismOfFinite D (towerSSData T) (fun p => (P.ambient p).hom)
    (fun p n => subobjectMorphism_exists _ _ _ (fun a ha =>
      (towerSSData_cycles T p n _).mpr ((P.cycles p n a).mp ha)))
    (fun p n => subobjectMorphism_exists _ _ _ (fun a ha =>
      (towerSSData_boundaries T p n _).mpr ((P.boundaries p n a).mp ha)))

private def presentationDataInverse (P : TowerSequencePresentation unit T D d) :
    SSDataMorphism (ℤ×ℤ) (towerSSData T) D :=
  dataMorphismOfFinite (towerSSData T) D (fun p => (P.ambient p).inv)
    (fun p n => subobjectMorphism_exists _ _ _ (fun a ha => by
      apply (P.cycles p n _).mpr
      rw [← ModuleCat.comp_apply,Iso.inv_hom_id]
      exact (towerSSData_cycles T p n _).mp ha))
    (fun p n => subobjectMorphism_exists _ _ _ (fun a ha => by
      apply (P.boundaries p n _).mpr
      rw [← ModuleCat.comp_apply,Iso.inv_hom_id]
      exact (towerSSData_boundaries T p n _).mp ha))

private def presentationPageIso (P : TowerSequencePresentation unit T D d)
    (p : ℤ×ℤ) (r : WithTop ℕ) : (D p).page r ≅ (towerSSData T p).page r where
  hom := (presentationDataMap P).pageMap p r
  inv := (presentationDataInverse P).pageMap p r
  hom_inv_id := by
    have hc : (presentationDataMap P).comp (presentationDataInverse P)=SSDataMorphism.id D := by
      apply SSDataMorphism.ext
      funext q
      exact (P.ambient q).hom_inv_id
    rw [← SSDataMorphism.pageMap_comp,hc,SSDataMorphism.pageMap_id]
  inv_hom_id := by
    have hc : (presentationDataInverse P).comp (presentationDataMap P)=SSDataMorphism.id (towerSSData T) := by
      apply SSDataMorphism.ext
      funext q
      exact (P.ambient q).inv_hom_id
    rw [← SSDataMorphism.pageMap_comp,hc,SSDataMorphism.pageMap_id]

private theorem presentationDataMap_cycle_value (P : TowerSequencePresentation unit T D d)
    (p : ℤ×ℤ) (n : ℕ) (z : (Subobject.underlying.obj ((D p).Z n) : ModuleCat ℤ)) :
    cycleRep T p n ((presentationDataMap P).cycleMap p n z) =
      ((P.ambient p).hom (((D p).Z n).arrow z)).val := by
  have hc := ConcreteCategory.congr_hom ((presentationDataMap P).cycleMap_arrow p n) z
  exact congrArg Subtype.val hc

private theorem presentationDataInverse_cycle_value (P : TowerSequencePresentation unit T D d)
    (p : ℤ×ℤ) (n : ℕ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z n) : ModuleCat ℤ)) :
    ((P.ambient p).hom (((D p).Z n).arrow ((presentationDataInverse P).cycleMap p n z))).val =
      cycleRep T p n z := by
  have hc := ConcreteCategory.congr_hom ((presentationDataInverse P).cycleMap_arrow p n) z
  change ((D p).Z n).arrow ((presentationDataInverse P).cycleMap p n z)=
    (P.ambient p).inv (((towerSSData T p).Z n).arrow z) at hc
  rw [hc,← ModuleCat.comp_apply,Iso.inv_hom_id]
  rfl

private theorem dataMap_page_value {D D' : (ℤ×ℤ) → SSData (ModuleCat.{v} ℤ)}
    (F : SSDataMorphism (ℤ×ℤ) D D') (p : ℤ×ℤ) (n : WithTop ℕ)
    (z : (Subobject.underlying.obj ((D p).Z n) : ModuleCat ℤ)) :
    F.pageMap p n ((D p).pageπ n z) = (D' p).pageπ n (F.cycleMap p n z) :=
  ConcreteCategory.congr_hom (F.pageπ_pageMap p n) z

private theorem presentationPageIso_differential (P : TowerSequencePresentation unit T D d)
    (r : ℤ) (hr : 2≤r) (p : ℤ×ℤ) :
    (presentationPageIso P p (↑(r-2).toNat : WithTop ℕ)).hom ≫ towerD T r p =
      d r p ≫ (presentationPageIso P (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ)).hom := by
  let n := (r-2).toNat
  let F := presentationDataMap P
  let G := presentationDataInverse P
  letI : Epi ((D p).pageπ (↑n : WithTop ℕ)) := by
    dsimp only [SSData.pageπ]; infer_instance
  apply (cancel_epi ((D p).pageπ (↑n : WithTop ℕ))).mp
  ext z
  change towerD T r p (F.pageMap p n ((D p).pageπ n z)) =
    F.pageMap (p+(r,r-1)) n (d r p ((D p).pageπ n z))
  rw [dataMap_page_value F,towerD_pageπ T r hr p]
  let zT := F.cycleMap p n z
  let a := cycleLiftAt T r hr p zT
  let wT := layerCycle T (p+(r,r-1)) n
    (degreeCast (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1) a)
  let wD := G.cycleMap (p+(r,r-1)) n wT
  have hd : d r p ((D p).pageπ n z) = (D (p+(r,r-1))).pageπ n wD := by
    apply P.differential r hr p z a wD
    · rw [← presentationDataMap_cycle_value P]
      exact (cycleLiftAt_spec T r hr p zT).symm
    · rw [presentationDataInverse_cycle_value P]
      exact (cycleRep_layerCycle T _ _ _).trans (by rw [degreeCast_apply])
  rw [hd]
  have hg := ConcreteCategory.congr_hom (G.pageπ_pageMap (p+(r,r-1)) n) wT
  change G.pageMap (p+(r,r-1)) n ((towerSSData T (p+(r,r-1))).pageπ n wT)=
    (D (p+(r,r-1))).pageπ n wD at hg
  rw [← hg]
  have hi := ConcreteCategory.congr_hom (presentationPageIso P (p+(r,r-1)) n).inv_hom_id
    ((towerSSData T (p+(r,r-1))).pageπ n wT)
  exact hi.symm

end PresentationComparison

section SyntheticWeightShift
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)] {HS : Syn}

private def weightTwistIso (a w : ℤ) (V : Syn) :
    (SyntheticCategory.biShift (0,-(w+a))).obj
        ((SyntheticCategory.biShift (0,a)).obj V) ≅
      (SyntheticCategory.biShift (0,-w)).obj V :=
  (biShiftAddIso (0,a) (0,-(w+a)) (0,-w) (by ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> omega)).app V

private def actualWeightShiftDataMap
    {F : KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily Syn}
    {synUnit : S_0_0 ⟶ HS} (P : SyntheticTowerPresentation synUnit F)
    (V : Syn) (a w : ℤ) : SSDataMorphism (ℤ×ℤ)
      (fun p => (F.obj V).sequence.ssData (p.1,p.2,w))
      (fun p => (F.obj ((SyntheticCategory.biShift (0,a)).obj V)).sequence.ssData (p.1,p.2,w+a)) :=
  (presentationDataMap (P.sequence V w)).comp
    ((towerSSDataMap (towerIsoMap
      (P.tower ((SyntheticCategory.biShift (0,-w)).obj V))
      (P.tower ((SyntheticCategory.biShift (0,-(w+a))).obj
        ((SyntheticCategory.biShift (0,a)).obj V))) (weightTwistIso a w V).symm)).comp
      (presentationDataInverse (P.sequence ((SyntheticCategory.biShift (0,a)).obj V) (w+a))))

private def actualWeightShiftPageIso
    {F : KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily Syn}
    {synUnit : S_0_0 ⟶ HS} (P : SyntheticTowerPresentation synUnit F)
    (V : Syn) (a w : ℤ) (p : ℤ×ℤ) (n : WithTop ℕ) :
      ((F.obj V).sequence.ssData (p.1,p.2,w)).page n ≅
      ((F.obj ((SyntheticCategory.biShift (0,a)).obj V)).sequence.ssData (p.1,p.2,w+a)).page n :=
  presentationPageIso (P.sequence V w) p n ≪≫
    towerPageIso (towerIsoMap
      (P.tower ((SyntheticCategory.biShift (0,-w)).obj V))
      (P.tower ((SyntheticCategory.biShift (0,-(w+a))).obj
        ((SyntheticCategory.biShift (0,a)).obj V))) (weightTwistIso a w V).symm)
      (fun j => inferInstanceAs (IsIso (towerStageIso _ _ _ j).hom)) p n ≪≫
    (presentationPageIso (P.sequence ((SyntheticCategory.biShift (0,a)).obj V) (w+a)) p n).symm

private theorem actualWeightShiftPageIso_hom
    {F : KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily Syn}
    {synUnit : S_0_0 ⟶ HS} (P : SyntheticTowerPresentation synUnit F)
    (V : Syn) (a w : ℤ) (p : ℤ×ℤ) (n : WithTop ℕ) :
    (actualWeightShiftPageIso P V a w p n).hom = (actualWeightShiftDataMap P V a w).pageMap p n := by
  simp only [actualWeightShiftPageIso,actualWeightShiftDataMap,Iso.trans_hom,
    SSDataMorphism.pageMap_comp,Iso.symm_hom,presentationPageIso,towerPageIso]

private theorem actualWeightShift_differential
    {F : KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily Syn}
    {synUnit : S_0_0 ⟶ HS} (P : SyntheticTowerPresentation synUnit F)
    (V : Syn) (a w r : ℤ) (hr : 2≤r) (p : ℤ×ℤ) :
    (actualWeightShiftDataMap P V a w).pageMap p (↑(r-2).toNat : WithTop ℕ) ≫
        fixedWeightDifferential (F.obj ((SyntheticCategory.biShift (0,a)).obj V)) (w+a) r p =
      fixedWeightDifferential (F.obj V) w r p ≫
        (actualWeightShiftDataMap P V a w).pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) := by
  let PA := P.sequence V w
  let PB := P.sequence ((SyntheticCategory.biShift (0,a)).obj V) (w+a)
  let e := (weightTwistIso a w V).symm
  let T := P.tower ((SyntheticCategory.biShift (0,-w)).obj V)
  let U := P.tower ((SyntheticCategory.biShift (0,-(w+a))).obj
    ((SyntheticCategory.biShift (0,a)).obj V))
  let J := towerSSDataMap (towerIsoMap T U e)
  let n : WithTop ℕ := ↑(r-2).toNat
  have hb : (presentationPageIso PB p n).inv ≫
      fixedWeightDifferential (F.obj ((SyntheticCategory.biShift (0,a)).obj V)) (w+a) r p =
      towerD U r p ≫ (presentationPageIso PB (p+(r,r-1)) n).inv := by
    apply (cancel_epi (presentationPageIso PB p n).hom).mp
    simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
    rw [presentationPageIso_differential PB r hr p]
    simp only [n,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hj := towerSSDataMorphism_differential (towerIsoMap T U e) J (fun _ => rfl) r p
  have ha := presentationPageIso_differential PA r hr p
  change J.pageMap p n ≫ towerD U r p = towerD T r p ≫ J.pageMap (p+(r,r-1)) n at hj
  change (presentationPageIso PA p n).hom ≫ towerD T r p =
    fixedWeightDifferential (F.obj V) w r p ≫ (presentationPageIso PA (p+(r,r-1)) n).hom at ha
  simp only [actualWeightShiftDataMap,SSDataMorphism.pageMap_comp]
  change ((presentationPageIso PA p n).hom ≫
    J.pageMap p n ≫ (presentationPageIso PB p n).inv) ≫ _ =
    _ ≫ ((presentationPageIso PA (p+(r,r-1)) n).hom ≫
      J.pageMap (p+(r,r-1)) n ≫ (presentationPageIso PB (p+(r,r-1)) n).inv)
  rw [Category.assoc,Category.assoc,hb,← Category.assoc (J.pageMap p n),hj]
  simp only [← Category.assoc]
  rw [ha]


end SyntheticWeightShift

end
end KIP126.AdamsSynthetic.Internal.Source

namespace KIP126.AdamsSynthetic.SyntheticTowerPresentation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic.Internal.Source
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)] {HS : Syn}
  {synUnit : S_0_0 ⟶ HS} {F : SyntheticAdamsFamily Syn}

/-- The actual coefficient towers identify weight `w` on `V` with weight
`w + a` on its weight suspension. The comparison retains every finite and
infinite cycle and boundary subobject. -/
@[no_expose] public def weightShift (P : SyntheticTowerPresentation synUnit F)
    (V : Syn) (a w : ℤ) : SSDataMorphism (ℤ×ℤ)
      (fun p => (F.obj V).sequence.ssData (p.1,p.2,w))
      (fun p => (F.obj ((SyntheticCategory.biShift (0,a)).obj V)).sequence.ssData (p.1,p.2,w+a)) :=
  actualWeightShiftDataMap P V a w

/-- Every page of the actual weight-shift comparison is an isomorphism. -/
public theorem weightShift_isIso (P : SyntheticTowerPresentation synUnit F)
    (V : Syn) (a w : ℤ) (p : ℤ×ℤ) (n : WithTop ℕ) :
    IsIso ((P.weightShift V a w).pageMap p n) := by
  change IsIso ((actualWeightShiftDataMap P V a w).pageMap p n)
  rw [← actualWeightShiftPageIso_hom]
  infer_instance

/-- The same representative comparison preserves the actual lift-and-cofiber
differential at every page starting at page two. -/
public theorem weightShift_differential (P : SyntheticTowerPresentation synUnit F)
    (V : Syn) (a w r : ℤ) (hr : 2≤r) (p : ℤ×ℤ) :
    (P.weightShift V a w).pageMap p (↑(r-2).toNat : WithTop ℕ) ≫
        fixedWeightDifferential (F.obj ((SyntheticCategory.biShift (0,a)).obj V)) (w+a) r p =
      fixedWeightDifferential (F.obj V) w r p ≫
        (P.weightShift V a w).pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) :=
  actualWeightShift_differential P V a w r hr p

end
end KIP126.AdamsSynthetic.SyntheticTowerPresentation
