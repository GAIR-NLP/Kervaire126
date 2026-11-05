module
import KIP126.AdamsSynthetic.Tower
import KIP126.AdamsSynthetic.Quotients
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Triangulated.Functor

/-! An intrinsic spectral sequence of the lambda tower.

The raw exact couple retains its first differential. The lambda-side
construction uses the Adams page numbering and trigrading.
-/

/- The raw exact couple starts at E₁ with d₁, from the supplied tower
objects and maps. -/
@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence KIP126.AdamsSynthetic
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option Elab.async false
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
private structure RawTower (C : Type u) [Category.{v} C] where
  stage : ℕ → C
  map : ∀ {s t : ℕ}, s ≤ t → (stage t ⟶ stage s)
  map_self : ∀ s, map (le_refl s) = 𝟙 _
  map_comp : ∀ {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t),
    map hst ≫ map hrs = map (hrs.trans hst)
namespace RawTower
variable (T : RawTower C)
private abbrev stageAt (s : ℤ) := T.stage s.toNat
private def mapAt {s t : ℤ} (h : s ≤ t) : T.stageAt t ⟶ T.stageAt s :=
  T.map (show s.toNat ≤ t.toNat by omega)
private def layer (s : ℤ) := HasFunctorialCofiber.cofib (T.mapAt (show s ≤ s + 1 by omega))
private abbrev FirstPage (p : ℤ × ℤ) := HomotopyGroup (p.2 - p.1) (T.layer p.1)
private def layerMap (p : ℤ × ℤ) :
    HomotopyGroup (p.2 - p.1) (T.stageAt p.1) →ₗ[ℤ] T.FirstPage p :=
  (inducedMap (HasFunctorialCofiber.cofibι (T.mapAt (show p.1 ≤ p.1 + 1 by omega)))
    (p.2 - p.1)).toIntLinearMap

/-- Desuspension uses the shift structure of this category. -/
private def desuspend (Y : C) (n : ℤ) :
    HomotopyGroup n (Y⟦(1 : ℤ)⟧) →+ HomotopyGroup (n - 1) Y where
  toFun z := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
    (shiftFunctor C (-1)).map z ≫ (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app Y
  map_zero' := by simp only [Functor.map_zero, zero_comp, comp_zero]
  map_add' a b := by rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private def connecting (p : ℤ × ℤ) : T.FirstPage p →ₗ[ℤ]
    HomotopyGroup (p.2 - p.1 - 1) (T.stageAt (p.1 + 1)) :=
  ((desuspend (T.stageAt (p.1 + 1)) (p.2 - p.1)).comp
    (inducedMap (HasFunctorialCofiber.cofibδ (T.mapAt (show p.1 ≤ p.1 + 1 by omega)))
      (p.2 - p.1))).toIntLinearMap

private def cycles (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    Submodule ℤ (T.FirstPage p) :=
  (LinearMap.range (inducedMap (T.mapAt (show p.1 + 1 ≤ p.1 + r by omega))
    (p.2 - p.1 - 1)).toIntLinearMap).comap (T.connecting p)
private def boundaries (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    Submodule ℤ (T.FirstPage p) :=
  (LinearMap.ker (inducedMap (T.mapAt (show p.1 - r + 1 ≤ p.1 by omega))
    (p.2 - p.1)).toIntLinearMap).map (T.layerMap p)


end RawTower

private noncomputable def towerI (T : RawTower C) (m s t : ℤ) (h : s ≤ t) :
    HomotopyGroup m (T.stageAt t) →ₗ[ℤ] HomotopyGroup m (T.stageAt s) :=
  (inducedMap (T.mapAt h) m).toIntLinearMap

private theorem towerI_comp (T : RawTower C) (m s t z : ℤ)
    (hst : s ≤ t) (htz : t ≤ z) (a : HomotopyGroup m (T.stageAt z)) :
    towerI T m s t hst (towerI T m t z htz a) = towerI T m s z (hst.trans htz) a := by
  change (a ≫ T.mapAt htz) ≫ T.mapAt hst = a ≫ T.mapAt (hst.trans htz)
  rw [Category.assoc]
  congr 1
  exact T.map_comp _ _

private abbrev cycleAmbient (T : RawTower C) (p : ℤ × ℤ) :=
  T.cycles 1 (by decide) p

private noncomputable def finiteCycles (T : RawTower C) (p : ℤ × ℤ) (n : ℕ) :
    Submodule ℤ (cycleAmbient T p) :=
  (T.cycles (n + 1) (by omega) p).comap (T.cycles 1 (by decide) p).subtype

private noncomputable def finiteBoundaries (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) : Submodule ℤ (cycleAmbient T p) :=
  (T.boundaries (n + 1) (by omega) p).comap (T.cycles 1 (by decide) p).subtype

private noncomputable def allCycles (T : RawTower C) (p : ℤ × ℤ) :
    WithTop ℕ → Submodule ℤ (cycleAmbient T p)
  | ⊤ => ⨅ n : ℕ, finiteCycles T p n
  | (n : ℕ) => finiteCycles T p n

private noncomputable def allBoundaries (T : RawTower C) (p : ℤ × ℤ) :
    WithTop ℕ → Submodule ℤ (cycleAmbient T p)
  | ⊤ => ⨆ n : ℕ, finiteBoundaries T p n
  | (n : ℕ) => finiteBoundaries T p n

private theorem finiteCycles_antitone (T : RawTower C) (p : ℤ × ℤ) :
    Antitone (finiteCycles T p) := by
  intro i j hij x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨towerI T (p.2-p.1-1) (p.1+(i+1:ℕ)) (p.1+(j+1:ℕ)) (by omega) y, ?_⟩
  change towerI T (p.2-p.1-1) (p.1+1) (p.1+(i+1:ℕ)) _ _ = _
  rw [towerI_comp]
  exact hy

private theorem finiteBoundaries_monotone (T : RawTower C) (p : ℤ × ℤ) :
    Monotone (finiteBoundaries T p) := by
  intro i j hij x hx
  obtain ⟨y, hy, hj⟩ := hx
  refine ⟨y, ?_, hj⟩
  change towerI T (p.2-p.1) (p.1-(i+1:ℕ)+1) p.1 _ y = 0 at hy
  change towerI T (p.2-p.1) (p.1-(j+1:ℕ)+1) p.1 _ y = 0
  rw [← towerI_comp T (p.2-p.1) (p.1-(j+1:ℕ)+1)
    (p.1-(i+1:ℕ)+1) p.1 (by omega) (by omega), hy, map_zero]

private theorem connecting_layerMap (T : RawTower C) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    T.connecting p (T.layerMap p a) = 0 := by
  let f := T.mapAt (show p.1 ≤ p.1+1 by omega)
  have hzero : HasFunctorialCofiber.cofibι f ≫ HasFunctorialCofiber.cofibδ f = 0 :=
    comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished f)
  change (RawTower.desuspend _ _)
    ((a ≫ HasFunctorialCofiber.cofibι f) ≫ HasFunctorialCofiber.cofibδ f) = 0
  rw [Category.assoc, hzero, comp_zero, map_zero]

private theorem finiteBoundaries_le_cycles (T : RawTower C) (p : ℤ × ℤ)
    (i j : ℕ) : finiteBoundaries T p i ≤ finiteCycles T p j := by
  intro x hx
  obtain ⟨y, _, hj⟩ := hx
  change T.layerMap p y = x.val at hj
  change T.connecting p x.val ∈ LinearMap.range _
  rw [← hj, connecting_layerMap]
  exact Submodule.zero_mem _

private theorem allCycles_antitone (T : RawTower C) (p : ℤ × ℤ) :
    Antitone (allCycles T p) := by
  intro i j hij
  cases i using WithTop.recTopCoe with
  | top => have h : j = ⊤ := top_le_iff.mp hij; subst j; exact le_rfl
  | coe i =>
    cases j using WithTop.recTopCoe with
    | top => exact iInf_le _ i
    | coe j => exact finiteCycles_antitone T p (WithTop.coe_le_coe.mp hij)

private theorem allBoundaries_monotone (T : RawTower C) (p : ℤ × ℤ) :
    Monotone (allBoundaries T p) := by
  intro i j hij
  cases i using WithTop.recTopCoe with
  | top => have h : j = ⊤ := top_le_iff.mp hij; subst j; exact le_rfl
  | coe i =>
    cases j using WithTop.recTopCoe with
    | top => exact le_iSup (finiteBoundaries T p) i
    | coe j => exact finiteBoundaries_monotone T p (WithTop.coe_le_coe.mp hij)

private theorem allBoundaries_le_cycles (T : RawTower C) (p : ℤ × ℤ)
    (r : WithTop ℕ) : allBoundaries T p r ≤ allCycles T p r := by
  cases r using WithTop.recTopCoe with
  | top => exact iSup_le fun i => le_iInf fun j => finiteBoundaries_le_cycles T p i j
  | coe n => exact finiteBoundaries_le_cycles T p n n

private noncomputable def towerSSData (T : RawTower C) (p : ℤ × ℤ) :
    SSData (ModuleCat.{v} ℤ) where
  V := ModuleCat.of ℤ (cycleAmbient T p)
  Z r := (ModuleCat.subobjectModule _).symm (allCycles T p r)
  B r := (ModuleCat.subobjectModule _).symm (allBoundaries T p r)
  Z_anti := (ModuleCat.subobjectModule _).symm.monotone.comp_antitone (allCycles_antitone T p)
  B_mono := (ModuleCat.subobjectModule _).symm.monotone.comp (allBoundaries_monotone T p)
  Z_zero := by
    change (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm
      ((T.cycles 1 (by decide) p).comap (T.cycles 1 (by decide) p).subtype) = ⊤
    rw [Submodule.comap_subtype_self, OrderIso.map_top]
  B_le_Z r := (ModuleCat.subobjectModule _).symm.monotone (allBoundaries_le_cycles T p r)
  Z_top_greatest A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) A ≤ (ModuleCat.subobjectModule _)
      ((ModuleCat.subobjectModule _).symm _)
    rw [OrderIso.apply_symm_apply]
    refine le_iInf fun n => ?_
    have hn := (ModuleCat.subobjectModule _).monotone (h n)
    rw [OrderIso.apply_symm_apply] at hn
    exact hn
  B_top_least A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) ((ModuleCat.subobjectModule _).symm _) ≤
      (ModuleCat.subobjectModule _) A
    rw [OrderIso.apply_symm_apply]
    refine iSup_le fun n => ?_
    have hn := (ModuleCat.subobjectModule _).monotone (h n)
    rw [OrderIso.apply_symm_apply] at hn
    exact hn

private theorem towerSSData_cycles (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) (a : (towerSSData T p).V) :
    a ∈ (ModuleCat.subobjectModule _ ((towerSSData T p).Z n)) ↔
      a.val ∈ T.cycles (n + 1) (by omega) p := by
  change a ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p)))
    ((ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm
      (finiteCycles T p n)) ↔ _
  rw [OrderIso.apply_symm_apply]
  rfl

private theorem towerSSData_boundaries (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) (a : (towerSSData T p).V) :
    a ∈ (ModuleCat.subobjectModule _ ((towerSSData T p).B n)) ↔
      a.val ∈ T.boundaries (n + 1) (by omega) p := by
  change a ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p)))
    ((ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm
      (finiteBoundaries T p n)) ↔ _
  rw [OrderIso.apply_symm_apply]
  rfl

private theorem support_layerMap_exact (T : RawTower C) (p : ℤ × ℤ)
    (y : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    T.layerMap p y = 0 ↔
      ∃ z : HomotopyGroup (p.2-p.1) (T.stageAt (p.1+1)),
        z ≫ T.mapAt (show p.1 ≤ p.1+1 by omega) = y := by
  let f := T.mapAt (show p.1 ≤ p.1+1 by omega)
  change y ≫ HasFunctorialCofiber.cofibι f = 0 ↔ ∃ z, z ≫ f = y
  constructor
  · intro hy
    obtain ⟨z,hz⟩ := Triangle.coyoneda_exact₂ _
      (HasFunctorialCofiber.cofib_distinguished f) y hy
    exact ⟨z,hz.symm⟩
  · rintro ⟨z,rfl⟩
    have hzero : f ≫ HasFunctorialCofiber.cofibι f = 0 :=
      comp_distTriang_mor_zero₁₂ _ (HasFunctorialCofiber.cofib_distinguished f)
    rw [Category.assoc, hzero, comp_zero]

private theorem support_connecting_exact (T : RawTower C) (p : ℤ × ℤ)
    (x : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+1))) :
    x ≫ T.mapAt (show p.1 ≤ p.1+1 by omega) = 0 ↔
      ∃ z : T.FirstPage p, T.connecting p z = x := by
  let f := T.mapAt (show p.1 ≤ p.1+1 by omega)
  let F := shiftFunctor C (-1 : ℤ)
  let a := (shiftFunctorAdd' C (p.2-p.1) (-1) (p.2-p.1-1) (by omega)).app SphereSpectrum
  let b := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
  let bX := b.app (T.stageAt (p.1+1))
  let bY := b.app (T.stageAt p.1)
  have hc (z : T.FirstPage p) :
      T.connecting p z = a.hom ≫ F.map (z ≫ HasFunctorialCofiber.cofibδ f) ≫ bX.hom := by
    change a.hom ≫ F.map (z ≫ _) ≫ bX.hom = _
    rfl
  have hb : bX.inv ≫ F.map ((shiftFunctor C (1 : ℤ)).map f) =
      f ≫ bY.inv := (b.inv.naturality f).symm
  constructor
  · intro hx
    change x ≫ f = 0 at hx
    let w := F.preimage (a.inv ≫ x ≫ bX.inv)
    have hw : F.map w = a.inv ≫ x ≫ bX.inv := F.map_preimage _
    have hwf : w ≫ (shiftFunctor C (1 : ℤ)).map f = 0 := by
      apply F.map_injective
      rw [Functor.map_comp, hw, Functor.map_zero]
      simp only [Category.assoc, hb, ← Category.assoc x f, hx, zero_comp, comp_zero]
    obtain ⟨z,hz⟩ := Triangle.coyoneda_exact₁ _
      (HasFunctorialCofiber.cofib_distinguished f) w hwf
    change w = z ≫ HasFunctorialCofiber.cofibδ f at hz
    change HomotopyGroup (p.2-p.1) (T.layer p.1) at z
    refine ⟨z, ?_⟩
    rw [hc, ← hz, hw]
    simp
  · rintro ⟨z,rfl⟩
    change T.connecting p z ≫ f = 0
    rw [hc]
    have hb' : bX.hom ≫ f = F.map ((shiftFunctor C (1 : ℤ)).map f) ≫ bY.hom :=
      (b.hom.naturality f).symm
    have hzero : HasFunctorialCofiber.cofibδ f ≫ (shiftFunctor C (1 : ℤ)).map f = 0 :=
      comp_distTriang_mor_zero₃₁ _ (HasFunctorialCofiber.cofib_distinguished f)
    simp only [Category.assoc, hb', ← F.map_comp_assoc, hzero, comp_zero,
      F.map_zero, zero_comp]

private theorem support_mapAt_comp (T : RawTower C) {a b c : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    T.mapAt hbc ≫ T.mapAt hab = T.mapAt (hab.trans hbc) := T.map_comp _ _

private theorem support_layer_boundary_iff (T : RawTower C)
    (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (y : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    T.layerMap p y ∈ T.boundaries r hr p ↔
      ∃ z : HomotopyGroup (p.2-p.1) (T.stageAt (p.1+1)),
        z ≫ T.mapAt (show p.1-r+1 ≤ p.1+1 by omega) =
          y ≫ T.mapAt (show p.1-r+1 ≤ p.1 by omega) := by
  constructor
  · rintro ⟨w, hw, hj⟩
    have he : T.layerMap p (y-w) = 0 := by
      rw [map_sub, hj, sub_self]
    obtain ⟨z,hz⟩ := (support_layerMap_exact T p (y-w)).mp he
    refine ⟨z, ?_⟩
    rw [← support_mapAt_comp T (show p.1-r+1 ≤ p.1 by omega)
      (show p.1 ≤ p.1+1 by omega), ← Category.assoc, hz, Preadditive.sub_comp]
    change w ≫ T.mapAt (show p.1-r+1 ≤ p.1 by omega) = 0 at hw
    rw [hw, sub_zero]
  · rintro ⟨z,hz⟩
    let w := y - z ≫ T.mapAt (show p.1 ≤ p.1+1 by omega)
    refine ⟨w, ?_, ?_⟩
    · change w ≫ T.mapAt (show p.1-r+1 ≤ p.1 by omega) = 0
      dsimp only [w]
      rw [Preadditive.sub_comp, Category.assoc, support_mapAt_comp, hz, sub_self]
    · dsimp only [w]
      rw [map_sub, (support_layerMap_exact T p _).mpr ⟨z,rfl⟩, sub_zero]


private theorem support_kernel_of_representative
    (D E : SSData (ModuleCat.{v} ℤ)) (n : ℕ) (d : D.page ↑n ⟶ E.page ↑n)
    (h : ∀ z : (Subobject.underlying.obj (D.Z ↑n) : ModuleCat ℤ),
      d (D.pageπ ↑n z) = 0 ↔
        (D.Z ↑n).arrow z ∈ (ModuleCat.subobjectModule _) (D.Z ↑(n+1))) :
    kernelSubobject d = imageSubobject (Subobject.ofLE
      (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        D.pageπ ↑n) := by
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n)
    (D.Z_anti (by exact_mod_cast Nat.le_succ n))
  have hi (y : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat ℤ)) :
      (D.Z ↑n).arrow (i y) = (D.Z ↑(n+1)).arrow y :=
    ConcreteCategory.congr_hom (Subobject.ofLE_arrow _) y
  apply (ModuleCat.subobjectModule _).injective
  rw [subobjectModule_kernel, subobjectModule_image]
  ext z
  change d z = 0 ↔ ∃ y, D.pageπ ↑n (i y) = z
  constructor
  · intro hz
    letI : Epi (D.pageπ ↑n) := by dsimp only [SSData.pageπ]; infer_instance
    obtain ⟨w,rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ↑n)).mp inferInstance z
    obtain ⟨y,hy⟩ := (h w).mp hz
    refine ⟨y, congrArg (D.pageπ ↑n) ?_⟩
    apply (ModuleCat.mono_iff_injective (D.Z ↑n).arrow).mp inferInstance
    exact (hi y).trans hy
  · rintro ⟨y,rfl⟩
    exact (h (i y)).mpr ⟨y,(hi y).symm⟩

private theorem support_image_of_representative
    (A D : SSData (ModuleCat.{v} ℤ)) (n : ℕ) (d : A.page ↑n ⟶ D.page ↑n)
    (h : ∀ z : (Subobject.underlying.obj (D.Z ↑n) : ModuleCat ℤ),
      (∃ y, d y = D.pageπ ↑n z) ↔
        (D.Z ↑n).arrow z ∈ (ModuleCat.subobjectModule _) (D.B ↑(n+1))) :
    imageSubobject d = imageSubobject (Subobject.ofLE
      (D.B ↑(n+1)) (D.Z ↑n)
      (le_trans (D.B_le_Z ↑(n+1)) (D.Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
        D.pageπ ↑n) := by
  let i := Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑n)
    (le_trans (D.B_le_Z ↑(n+1)) (D.Z_anti (by exact_mod_cast Nat.le_succ n)))
  have hi (y : (Subobject.underlying.obj (D.B ↑(n+1)) : ModuleCat ℤ)) :
      (D.Z ↑n).arrow (i y) = (D.B ↑(n+1)).arrow y :=
    ConcreteCategory.congr_hom (Subobject.ofLE_arrow _) y
  apply (ModuleCat.subobjectModule _).injective
  rw [subobjectModule_image, subobjectModule_image]
  ext z
  change (∃ y, d y = z) ↔ ∃ y, D.pageπ ↑n (i y) = z
  constructor
  · intro hz
    letI : Epi (D.pageπ ↑n) := by dsimp only [SSData.pageπ]; infer_instance
    obtain ⟨w,rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ↑n)).mp inferInstance z
    obtain ⟨y,hy⟩ := (h w).mp hz
    refine ⟨y, congrArg (D.pageπ ↑n) ?_⟩
    apply (ModuleCat.mono_iff_injective (D.Z ↑n).arrow).mp inferInstance
    exact (hi y).trans hy
  · rintro ⟨y,rfl⟩
    exact (h (i y)).mpr ⟨y,(hi y).symm⟩


/-! Private representative maps for the fixed categorical quotient pages. -/
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

private noncomputable def cycleRep (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) : (Subobject.underlying.obj ((towerSSData T p).Z n) : ModuleCat ℤ) →ₗ[ℤ]
      T.FirstPage p :=
  (T.cycles 1 (by decide) p).subtype.comp ((towerSSData T p).Z n).arrow.hom

private theorem cycleRep_mem (T : RawTower C) (p : ℤ × ℤ) (n : ℕ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z n) : ModuleCat ℤ)) :
    cycleRep T p n z ∈ T.cycles (n+1) (by omega) p :=
  (towerSSData_cycles T p n _).mp (LinearMap.mem_range_self _ z)

private theorem cycles_ge_one (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) : T.cycles (n+1) (by omega) p ≤ T.cycles 1 (by decide) p := by
  intro x hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨towerI T (p.2-p.1-1) (p.1+1) (p.1+(n+1:ℕ)) (by omega) a, ?_⟩
  change towerI T (p.2-p.1-1) (p.1+1) (p.1+1) _ _ = _
  rw [towerI_comp]
  exact ha

private noncomputable def cycleLift (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) (x : T.FirstPage p) (hx : x ∈ T.cycles (n+1) (by omega) p) :
    (Subobject.underlying.obj ((towerSSData T p).Z n) : ModuleCat ℤ) :=
  Classical.choose ((towerSSData_cycles T p n ⟨x, cycles_ge_one T p n hx⟩).mpr hx)

private theorem cycleRep_cycleLift (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) (x : T.FirstPage p) (hx : x ∈ T.cycles (n+1) (by omega) p) :
    cycleRep T p n (cycleLift T p n x hx) = x := by
  exact congrArg Subtype.val (Classical.choose_spec
    ((towerSSData_cycles T p n ⟨x, cycles_ge_one T p n hx⟩).mpr hx))

private theorem cycleRep_injective (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) : Function.Injective (cycleRep T p n) :=
  Subtype.val_injective.comp ((ModuleCat.mono_iff_injective _).mp inferInstance)

private noncomputable def layerCycle (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) : HomotopyGroup (p.2-p.1) (T.stageAt p.1) →ₗ[ℤ]
      (Subobject.underlying.obj ((towerSSData T p).Z n) : ModuleCat ℤ) :=
  subobjectLift ((towerSSData T p).Z n)
    ((T.layerMap p).codRestrict (T.cycles 1 (by decide) p) (fun a => by
      change T.connecting p (T.layerMap p a) ∈ LinearMap.range _
      rw [connecting_layerMap]; exact Submodule.zero_mem _))
    (fun a => (towerSSData_cycles T p n _).mpr (by
      change T.connecting p (T.layerMap p a) ∈ LinearMap.range _
      rw [connecting_layerMap]; exact Submodule.zero_mem _))

private theorem cycleRep_layerCycle (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    cycleRep T p n (layerCycle T p n a) = T.layerMap p a := by
  change (((towerSSData T p).Z n).arrow
    (subobjectLift _ _ _ a) : cycleAmbient T p).val = _
  rw [subobjectLift_arrow]
  rfl

private noncomputable def layerPage (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) : HomotopyGroup (p.2-p.1) (T.stageAt p.1) →ₗ[ℤ]
      (towerSSData T p).page (n : WithTop ℕ) :=
  ((towerSSData T p).pageπ n).hom.comp (layerCycle T p n)

private theorem page_eq_zero_iff (T : RawTower C) (p : ℤ × ℤ) (n : ℕ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z n) : ModuleCat ℤ)) :
    (towerSSData T p).pageπ n z = 0 ↔
      cycleRep T p n z ∈ T.boundaries (n+1) (by omega) p := by
  exact (subobject_cokernel_π_eq_zero_iff _ _ _ z).trans (towerSSData_boundaries T p n _)

private theorem layerPage_eq_zero (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1))
    (ha : towerI T (p.2-p.1) (p.1-(n+1:ℕ)+1) p.1 (by omega) a = 0) :
    layerPage T p n a = 0 := by
  apply (page_eq_zero_iff T p n _).mpr
  rw [cycleRep_layerCycle]
  exact ⟨a, ha, rfl⟩

private theorem layerPage_eq (T : RawTower C) (p : ℤ × ℤ)
    (n : ℕ) (a b : HomotopyGroup (p.2-p.1) (T.stageAt p.1))
    (hab : towerI T (p.2-p.1) (p.1-(n+1:ℕ)+1) p.1 (by omega) a =
      towerI T (p.2-p.1) (p.1-(n+1:ℕ)+1) p.1 (by omega) b) :
    layerPage T p n a = layerPage T p n b := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact layerPage_eq_zero T p n (a-b) (by rw [map_sub, hab, sub_self])

private noncomputable def degreeCast {Y : C} {m n : ℤ} (e : m = n) :
    HomotopyGroup m Y ≃ₗ[ℤ] HomotopyGroup n Y := by
  subst n
  exact LinearEquiv.refl ℤ _

private theorem degreeCast_apply {Y : C} {m n : ℤ} (e : m = n)
    (a : HomotopyGroup m Y) :
    degreeCast e a = Eq.mp (congrArg (fun k => HomotopyGroup k Y) e) a := by
  subst n; rfl

private theorem towerI_degreeCast (T : RawTower C) {m n : ℤ}
    (e : m = n) (s t : ℤ) (h : s ≤ t) (a : HomotopyGroup m (T.stageAt t)) :
    towerI T n s t h (degreeCast e a) = degreeCast e (towerI T m s t h a) := by
  subst n; rfl

private theorem towerI_range_eq (T : RawTower C) (m a s t : ℤ)
    (hst : s=t) (has : a≤s) :
    LinearMap.range (towerI T m a s has) =
      LinearMap.range (towerI T m a t (by omega)) := by
  subst t
  rfl

private theorem cycle_lift_exists (T : RawTower C) (r : ℤ) (hr : 1 ≤ r)
    (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    ∃ a : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)),
      towerI T (p.2-p.1-1) (p.1+1) (p.1+r) (by omega) a =
        T.connecting p (cycleRep T p (r-1).toNat z) := by
  have hz := cycleRep_mem T p (r-1).toNat z
  change T.connecting p (cycleRep T p (r-1).toNat z) ∈
    LinearMap.range (towerI T (p.2-p.1-1) (p.1+1)
      (p.1+((r-1).toNat+1:ℕ)) _) at hz
  rw [towerI_range_eq T _ _ _ (p.1+r) (by omega)] at hz
  exact hz

private noncomputable def cycleLiftAt (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :=
  (cycle_lift_exists T r hr p z).choose

private theorem cycleLiftAt_spec (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    towerI T (p.2-p.1-1) (p.1+1) (p.1+r) (by omega) (cycleLiftAt T r hr p z) =
      T.connecting p (cycleRep T p (r-1).toNat z) :=
  (cycle_lift_exists T r hr p z).choose_spec

private noncomputable def differentialValue (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    (towerSSData T (p+(r,r-1))).page (↑(r-1).toNat : WithTop ℕ) :=
  layerPage T (p+(r,r-1)) (r-1).toNat
    (degreeCast (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)
      (cycleLiftAt T r hr p z))

private theorem differentialValue_of_lift (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (a : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)))
    (ha : towerI T (p.2-p.1-1) (p.1+1) (p.1+r) (by omega) a =
      T.connecting p (cycleRep T p (r-1).toNat z)) :
    differentialValue T r hr p z = layerPage T (p+(r,r-1)) (r-1).toNat
      (degreeCast (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1) a) := by
  apply layerPage_eq
  rw [towerI_degreeCast, towerI_degreeCast]
  apply congrArg (degreeCast _)
  have aux (s : ℤ) (hs : s = p.1+1) (h : s ≤ p.1+r) :
      towerI T (p.2-p.1-1) s (p.1+r) h (cycleLiftAt T r hr p z) =
        towerI T (p.2-p.1-1) s (p.1+r) h a := by
    subst s
    exact (cycleLiftAt_spec T r hr p z).trans ha.symm
  exact aux _ (by dsimp; omega) _

private theorem differentialValue_zero_connecting (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (hz : T.connecting p (cycleRep T p (r-1).toNat z) = 0) :
    differentialValue T r hr p z = 0 := by
  rw [differentialValue_of_lift T r hr p z 0 (by rw [map_zero, hz]), map_zero, map_zero]

private theorem differentialValue_add (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z w : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    differentialValue T r hr p (z+w) =
      differentialValue T r hr p z + differentialValue T r hr p w := by
  rw [differentialValue_of_lift T r hr p (z+w)
    (cycleLiftAt T r hr p z + cycleLiftAt T r hr p w) (by
      rw [map_add, cycleLiftAt_spec, cycleLiftAt_spec, map_add, map_add])]
  simp only [map_add]
  rfl

private theorem support_degreeCast_cast {Y : C} {m n : ℤ} (e : m = n)
    (e' : n = m) (a : HomotopyGroup m Y) :
    degreeCast e' (degreeCast e a) = a := by
  subst n
  rfl

private theorem support_towerI_image_eq_iff (T : RawTower C)
    (m a b s t : ℤ) (hab : a = b) (has : a ≤ s) (hat : a ≤ t)
    (x : HomotopyGroup m (T.stageAt s)) (y : HomotopyGroup m (T.stageAt t)) :
    towerI T m a s has x = towerI T m a t hat y ↔
      towerI T m b s (by omega) x = towerI T m b t (by omega) y := by
  subst b
  rfl

private theorem differentialValue_eq_zero_iff (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    differentialValue T r hr p z = 0 ↔
      cycleRep T p (r-1).toNat z ∈ T.cycles ((r-1).toNat+2) (by omega) p := by
  let q := p+(r,r-1)
  have e : p.2-p.1-1 = q.2-q.1 := by dsimp [q]; omega
  have hb : q.1-((r-1).toNat+1:ℕ)+1 = p.1+1 := by dsimp [q]; omega
  have hs : p.1+((r-1).toNat+2:ℕ) = q.1+1 := by dsimp [q]; omega
  constructor
  · intro h
    change (towerSSData T q).pageπ _ (layerCycle T q _ _) = 0 at h
    have hmem := (page_eq_zero_iff T q (r-1).toNat _).mp h
    rw [cycleRep_layerCycle] at hmem
    obtain ⟨w,hw⟩ := (support_layer_boundary_iff T ((r-1).toNat+1) (by omega) q
      (degreeCast e (cycleLiftAt T r hr p z))).mp hmem
    change towerI T (q.2-q.1) (q.1-((r-1).toNat+1:ℕ)+1) (q.1+1) _ w =
      towerI T (q.2-q.1) (q.1-((r-1).toNat+1:ℕ)+1) q.1 _
        (degreeCast e (cycleLiftAt T r hr p z)) at hw
    have hw := (support_towerI_image_eq_iff T _ _ _ _ _ hb _ _ _ _).mp hw
    have hw' := congrArg (degreeCast e.symm) hw
    rw [← towerI_degreeCast, ← towerI_degreeCast, support_degreeCast_cast] at hw'
    change T.connecting p (cycleRep T p (r-1).toNat z) ∈
      LinearMap.range (towerI T (p.2-p.1-1) (p.1+1)
        (p.1+((r-1).toNat+2:ℕ)) _)
    rw [towerI_range_eq T _ _ _ (q.1+1) hs]
    refine ⟨degreeCast e.symm w, ?_⟩
    exact hw'.trans (cycleLiftAt_spec T r hr p z)
  · intro hx
    change T.connecting p (cycleRep T p (r-1).toNat z) ∈
      LinearMap.range (towerI T (p.2-p.1-1) (p.1+1)
        (p.1+((r-1).toNat+2:ℕ)) _) at hx
    rw [towerI_range_eq T _ _ _ (q.1+1) hs] at hx
    obtain ⟨w,hw⟩ := hx
    change (towerSSData T q).pageπ _ (layerCycle T q _ _) = 0
    apply (page_eq_zero_iff T q (r-1).toNat _).mpr
    rw [cycleRep_layerCycle]
    apply (support_layer_boundary_iff T ((r-1).toNat+1) (by omega) q
      (degreeCast e (cycleLiftAt T r hr p z))).mpr
    refine ⟨degreeCast e w, ?_⟩
    change towerI T (q.2-q.1) (q.1-((r-1).toNat+1:ℕ)+1) (q.1+1) _
        (degreeCast e w) =
      towerI T (q.2-q.1) (q.1-((r-1).toNat+1:ℕ)+1) q.1 _
        (degreeCast e (cycleLiftAt T r hr p z))
    apply (support_towerI_image_eq_iff T _ _ _ _ _ hb _ _ _ _).mpr
    rw [towerI_degreeCast, towerI_degreeCast, hw]
    exact congrArg (degreeCast e) (cycleLiftAt_spec T r hr p z).symm


attribute [local irreducible] towerSSData

private def intLinearOfAddHom {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' n z := by
    simpa only [RingHom.id_apply, Int.cast_id] using map_intCast_smul f ℤ ℤ n z

private noncomputable def differentialOnCycles (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ) :
    (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ) →ₗ[ℤ]
      (towerSSData T (p+(r,r-1))).page (↑(r-1).toNat : WithTop ℕ) :=
  intLinearOfAddHom (show (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ) →+
      (towerSSData T (p+(r,r-1))).page (↑(r-1).toNat : WithTop ℕ) from
    { toFun := differentialValue T r hr p
      map_zero' := differentialValue_zero_connecting T r hr p 0 (by rw [map_zero, map_zero])
      map_add' := differentialValue_add T r hr p })

attribute [local semireducible] towerSSData

private theorem differentialOnCycles_boundary (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ) :
    Subobject.ofLE ((towerSSData T p).B (↑(r-1).toNat : WithTop ℕ))
      ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) ((towerSSData T p).B_le_Z _) ≫
      ModuleCat.ofHom (differentialOnCycles T r hr p) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  let i := Subobject.ofLE ((towerSSData T p).B (↑(r-1).toNat : WithTop ℕ))
    ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) ((towerSSData T p).B_le_Z _)
  change differentialValue T r hr p (i b) = 0
  apply differentialValue_zero_connecting
  have hb := (towerSSData_boundaries T p (r-1).toNat _).mp (LinearMap.mem_range_self
    ((towerSSData T p).B (↑(r-1).toNat : WithTop ℕ)).arrow.hom b)
  obtain ⟨a, _, ha⟩ := hb
  have he := congrArg (fun f => (f b).val) (Subobject.ofLE_arrow ((towerSSData T p).B_le_Z
    (↑(r-1).toNat : WithTop ℕ)))
  change cycleRep T p (r-1).toNat (i b) = _ at he
  rw [he, ← ha]
  exact connecting_layerMap T p a

/-- Every representative is evaluated through the same connecting map,
the same actual tower lift and the same cofiber projection. -/
private def TowerDifferentialRule (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (d : (towerSSData T p).page (↑(r - 1).toNat : WithTop ℕ) ⟶
      (towerSSData T (p + (r,r-1))).page (↑(r - 1).toNat : WithTop ℕ)) : Prop :=
  ∀ (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r - 1).toNat : WithTop ℕ)) :
        ModuleCat ℤ))
    (a : HomotopyGroup (p.2 - p.1 - 1) (T.stageAt (p.1 + r)))
    (z' : (Subobject.underlying.obj
        ((towerSSData T (p + (r,r-1))).Z (↑(r - 1).toNat : WithTop ℕ)) : ModuleCat ℤ)),
    T.connecting p ((((towerSSData T p).Z _).arrow z).val) =
      a ≫ T.mapAt (show p.1 + 1 ≤ p.1 + r by omega) →
    ((((towerSSData T (p + (r,r-1))).Z _).arrow z').val) =
      T.layerMap (p + (r,r-1))
        (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1 + r)))
          (by dsimp; omega : p.2 - p.1 - 1 = (p + (r,r-1)).2 - (p + (r,r-1)).1)) a) →
    d ((towerSSData T p).pageπ _ z) = (towerSSData T (p + (r,r-1))).pageπ _ z'

/-- Existence and well-definedness of the quotient-page differential
given by the lift/cofiber formula. -/
private theorem towerDifferential_exists (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ) :
    ∃ d : (towerSSData T p).page (↑(r - 1).toNat : WithTop ℕ) ⟶
        (towerSSData T (p + (r,r-1))).page (↑(r - 1).toNat : WithTop ℕ),
      TowerDifferentialRule T r hr p d := by
  let f := ModuleCat.ofHom (differentialOnCycles T r hr p)
  let d := cokernel.desc _ f (differentialOnCycles_boundary T r hr p)
  refine ⟨d, ?_⟩
  intro z a z' ha hz'
  have hd : (towerSSData T p).pageπ (↑(r-1).toNat : WithTop ℕ) ≫ d = f :=
    cokernel.π_desc _ _ _
  change ((towerSSData T p).pageπ _ ≫ d) z = _
  rw [hd]
  change differentialValue T r hr p z = _
  rw [differentialValue_of_lift T r hr p z a ha.symm]
  change (towerSSData T (p+(r,r-1))).pageπ _ (layerCycle _ _ _ _) = _
  congr 1
  apply cycleRep_injective
  rw [cycleRep_layerCycle, degreeCast_apply]
  exact hz'.symm

private noncomputable def towerD (T : RawTower C) (r : ℤ) (p : ℤ × ℤ) :
    (towerSSData T p).page (↑(r - 1).toNat : WithTop ℕ) ⟶
      (towerSSData T (p + (r,r-1))).page (↑(r - 1).toNat : WithTop ℕ) :=
  if hr : 1 ≤ r then (towerDifferential_exists T r hr p).choose else 0

private theorem towerD_rule (T : RawTower C) (r : ℤ) (hr : 1 ≤ r)
    (p : ℤ × ℤ) : TowerDifferentialRule T r hr p (towerD T r p) := by
  simpa only [towerD, dif_pos hr] using (towerDifferential_exists T r hr p).choose_spec

private theorem towerD_pageπ (T : RawTower C) (r : ℤ)
    (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    towerD T r p ((towerSSData T p).pageπ _ z) = differentialValue T r hr p z := by
  apply towerD_rule T r hr p z (cycleLiftAt T r hr p z)
    (layerCycle T (p+(r,r-1)) (r-1).toNat
      (degreeCast (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)
        (cycleLiftAt T r hr p z)))
  · exact (cycleLiftAt_spec T r hr p z).symm
  · exact (cycleRep_layerCycle T _ _ _).trans (by rw [degreeCast_apply])

private noncomputable def towerPreSS (T : RawTower C) :
    PreSS (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  r₀ := 1
  ssData := towerSSData T
  diffDeg r := (r,r-1)
  d := towerD T

private theorem towerD_comp (T : RawTower C) (r : ℤ) (p : ℤ × ℤ) :
    towerD T r p ≫ towerD T r (p + (r,r-1)) = 0 := by
  by_cases hr : 1 ≤ r
  · let D := towerSSData T p
    let n : WithTop ℕ := ↑(r-1).toNat
    letI : Epi (D.pageπ n) := coequalizer.π_epi
    apply (cancel_epi (D.pageπ n)).mp
    ext z
    change towerD T r (p+(r,r-1)) (towerD T r p (D.pageπ n z)) = 0
    rw [towerD_pageπ T r hr p]
    change towerD T r (p+(r,r-1)) ((towerSSData T (p+(r,r-1))).pageπ _ _) = 0
    rw [towerD_pageπ T r hr]
    apply differentialValue_zero_connecting
    rw [cycleRep_layerCycle, connecting_layerMap]
  · simp only [towerD, dif_neg hr, zero_comp]

private theorem support_boundaries_mono (T : RawTower C)
    (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (h : r ≤ t) (p : ℤ × ℤ) :
    T.boundaries r hr p ≤ T.boundaries t ht p := by
  rintro x ⟨a,ha,hj⟩
  refine ⟨a, ?_, hj⟩
  change towerI T (p.2-p.1) (p.1-r+1) p.1 _ a = 0 at ha
  change towerI T (p.2-p.1) (p.1-t+1) p.1 _ a = 0
  rw [← towerI_comp T (p.2-p.1) (p.1-t+1) (p.1-r+1) p.1 (by omega) (by omega),
    ha, map_zero]

private theorem support_differential_layer_next_boundary (T : RawTower C)
    (r : ℤ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    T.layerMap (p+(r,r-1))
      (degreeCast (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)
        (cycleLiftAt T r hr p z)) ∈
      T.boundaries ((r-1).toNat+2) (by omega) (p+(r,r-1)) := by
  refine ⟨_, ?_, rfl⟩
  change towerI T ((p+(r,r-1)).2-(p+(r,r-1)).1)
    ((p+(r,r-1)).1-((r-1).toNat+2:ℕ)+1) (p+(r,r-1)).1 _
      (degreeCast _ _) = 0
  rw [towerI_degreeCast]
  change degreeCast _ (towerI T (p.2-p.1-1)
    ((p+(r,r-1)).1-((r-1).toNat+2:ℕ)+1) (p.1+r) _ (cycleLiftAt T r hr p z)) = 0
  have aux (s : ℤ) (hs : s = p.1) (h : s ≤ p.1+r) :
      towerI T (p.2-p.1-1) s (p.1+r) h (cycleLiftAt T r hr p z) = 0 := by
    subst s
    rw [← towerI_comp T (p.2-p.1-1) p.1 (p.1+1) (p.1+r) (by omega) (by omega),
      cycleLiftAt_spec]
    exact (support_connecting_exact T p _).mpr ⟨cycleRep T p (r-1).toNat z,rfl⟩
  rw [aux _ (by dsimp; omega) _, map_zero]

private theorem support_differentialValue_range_implies (T : RawTower C)
    (r : ℤ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (w : (Subobject.underlying.obj ((towerSSData T (p+(r,r-1))).Z
      (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    (∃ z : (Subobject.underlying.obj ((towerSSData T p).Z
      (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ),
      differentialValue T r hr p z = (towerSSData T (p+(r,r-1))).pageπ _ w) →
      cycleRep T (p+(r,r-1)) (r-1).toNat w ∈
        T.boundaries ((r-1).toNat+2) (by omega) (p+(r,r-1)) := by
  let e : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1 := by dsimp; omega
  rintro ⟨z,hz⟩
  let l := layerCycle T (p+(r,r-1)) ((r-1).toNat) (degreeCast e (cycleLiftAt T r hr p z))
  have he : (towerSSData T (p+(r,r-1))).pageπ ((r-1).toNat) (l-w) = 0 := by
    rw [map_sub]
    change differentialValue T r hr p z - (towerSSData T (p+(r,r-1))).pageπ ((r-1).toNat) w = 0
    rw [hz,sub_self]
  have hb := (page_eq_zero_iff T (p+(r,r-1)) ((r-1).toNat) (l-w)).mp he
  have hnext := support_differential_layer_next_boundary T r hr p z
  have hl : cycleRep T (p+(r,r-1)) ((r-1).toNat) l = T.layerMap (p+(r,r-1)) (degreeCast e (cycleLiftAt T r hr p z)) :=
    cycleRep_layerCycle T (p+(r,r-1)) ((r-1).toNat) _
  change T.layerMap (p+(r,r-1)) (degreeCast e (cycleLiftAt T r hr p z)) ∈ T.boundaries (((r-1).toNat)+2) _ (p+(r,r-1)) at hnext
  rw [← hl] at hnext
  have hb' := support_boundaries_mono T (((r-1).toNat)+1) (((r-1).toNat)+2) (by omega) (by omega) (by omega) (p+(r,r-1)) hb
  have hs := (T.boundaries (((r-1).toNat)+2) (by omega) (p+(r,r-1))).sub_mem hnext hb'
  change cycleRep T (p+(r,r-1)) ((r-1).toNat) w ∈ T.boundaries (((r-1).toNat)+2) (by omega) (p+(r,r-1))
  simpa only [map_sub, sub_sub_cancel] using hs

private theorem support_towerI_zero_index (T : RawTower C)
    (m a b s : ℤ) (hab : a=b) (has : a≤s)
    (y : HomotopyGroup m (T.stageAt s)) :
    towerI T m a s has y = 0 ↔ towerI T m b s (by omega) y = 0 := by
  subst b
  rfl

private theorem support_degreeCast_symm {Y : C} {m n : ℤ} (e : m=n) :
    (degreeCast e.symm : HomotopyGroup n Y ≃ₗ[ℤ] HomotopyGroup m Y) =
      (degreeCast e).symm := by
  subst n
  rfl

private theorem support_differentialValue_range_of_boundary (T : RawTower C)
    (r : ℤ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (w : (Subobject.underlying.obj ((towerSSData T (p+(r,r-1))).Z
      (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (hw : cycleRep T (p+(r,r-1)) (r-1).toNat w ∈
      T.boundaries ((r-1).toNat+2) (by omega) (p+(r,r-1))) :
    ∃ z : (Subobject.underlying.obj ((towerSSData T p).Z
      (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ),
      differentialValue T r hr p z = (towerSSData T (p+(r,r-1))).pageπ _ w := by
  let e : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1 := by dsimp; omega
  obtain ⟨a,ha,hj⟩ := hw
  change towerI T ((p+(r,r-1)).2-(p+(r,r-1)).1) ((p+(r,r-1)).1-(((r-1).toNat)+2:ℕ)+1) (p+(r,r-1)).1 _ a = 0 at ha
  have ha' : towerI T ((p+(r,r-1)).2-(p+(r,r-1)).1) p.1 (p+(r,r-1)).1 (by dsimp; omega) a = 0 :=
    (support_towerI_zero_index T _ _ p.1 _ (by dsimp; omega) _ a).mp ha
  let a' : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)) := degreeCast e.symm a
  have hai : towerI T (p.2-p.1-1) p.1 (p.1+r) (by omega) a' = 0 := by
    change towerI T (p.2-p.1-1) p.1 (p+(r,r-1)).1 _ (degreeCast e.symm a) = 0
    rw [towerI_degreeCast, ha', map_zero]
  let b := towerI T (p.2-p.1-1) (p.1+1) (p.1+r) (by omega) a'
  have hb : b ≫ T.mapAt (show p.1 ≤ p.1+1 by omega) = 0 := by
    change towerI T (p.2-p.1-1) p.1 (p.1+1) _ b = 0
    dsimp only [b]
    rw [towerI_comp, hai]
  obtain ⟨x,hx⟩ := (support_connecting_exact T p b).mp hb
  have hcx : x ∈ T.cycles (((r-1).toNat)+1) (by omega) p := by
    change T.connecting p x ∈ LinearMap.range
      (towerI T (p.2-p.1-1) (p.1+1) (p.1+(((r-1).toNat)+1:ℕ)) _)
    rw [towerI_range_eq T _ _ _ (p.1+r) (by dsimp; omega)]
    exact ⟨a',hx.symm⟩
  let z := cycleLift T p ((r-1).toNat) x hcx
  refine ⟨z, ?_⟩
  rw [differentialValue_of_lift T r hr p z a' (by
    rw [show cycleRep T p ((r-1).toNat) z = x from cycleRep_cycleLift T p ((r-1).toNat) x hcx]
    exact hx.symm)]
  change (towerSSData T (p+(r,r-1))).pageπ ((r-1).toNat) (layerCycle T (p+(r,r-1)) ((r-1).toNat) (degreeCast e a')) =
    (towerSSData T (p+(r,r-1))).pageπ ((r-1).toNat) w
  apply congrArg ((towerSSData T (p+(r,r-1))).pageπ ((r-1).toNat))
  apply cycleRep_injective T (p+(r,r-1)) ((r-1).toNat)
  rw [cycleRep_layerCycle]
  have hacast : degreeCast e a' = a := by
    change degreeCast e (degreeCast e.symm a) = a
    rw [support_degreeCast_symm e]
    exact LinearEquiv.apply_symm_apply _ _
  exact (congrArg (T.layerMap (p+(r,r-1))) hacast).trans hj

private theorem support_differentialValue_range_iff (T : RawTower C)
    (r : ℤ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (w : (Subobject.underlying.obj ((towerSSData T (p+(r,r-1))).Z
      (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    (∃ z : (Subobject.underlying.obj ((towerSSData T p).Z
      (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ),
      differentialValue T r hr p z = (towerSSData T (p+(r,r-1))).pageπ _ w) ↔
      cycleRep T (p+(r,r-1)) (r-1).toNat w ∈
        T.boundaries ((r-1).toNat+2) (by omega) (p+(r,r-1)) :=
  ⟨support_differentialValue_range_implies T r hr p w,
    support_differentialValue_range_of_boundary T r hr p w⟩

private theorem support_towerD_range_iff (T : RawTower C)
    (r : ℤ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (w : (Subobject.underlying.obj ((towerSSData T (p+(r,r-1))).Z
      (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ)) :
    (∃ y, towerD T r p y = (towerSSData T (p+(r,r-1))).pageπ _ w) ↔
      cycleRep T (p+(r,r-1)) (r-1).toNat w ∈
        T.boundaries ((r-1).toNat+2) (by omega) (p+(r,r-1)) := by
  rw [← support_differentialValue_range_iff T r hr p w]
  constructor
  · rintro ⟨y,hy⟩
    letI : Epi ((towerSSData T p).pageπ (↑(r-1).toNat : WithTop ℕ)) := by
      dsimp only [SSData.pageπ]; infer_instance
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective
      ((towerSSData T p).pageπ (↑(r-1).toNat : WithTop ℕ))).mp inferInstance y
    exact ⟨z, (towerD_pageπ T r hr p z).symm.trans hy⟩
  · rintro ⟨z,hz⟩
    exact ⟨(towerSSData T p).pageπ _ z, (towerD_pageπ T r hr p z).trans hz⟩

private theorem support_towerD_image (T : RawTower C) (r : ℤ)
    (p : ℤ × ℤ) (hr : 1 ≤ r) :
    let n := (r - 1).toNat
    let D := towerSSData T (p + (r,r-1))
    imageSubobject (towerD T r p) =
      imageSubobject (Subobject.ofLE (D.B ↑(n + 1)) (D.Z ↑n)
        (le_trans (D.B_le_Z ↑(n + 1))
          (D.Z_anti (by exact_mod_cast Nat.le_succ n))) ≫ D.pageπ ↑n) := by
  apply support_image_of_representative (towerSSData T p)
    (towerSSData T (p+(r,r-1))) (r-1).toNat (towerD T r p)
  intro w
  exact (support_towerD_range_iff T r hr p w).trans
    (towerSSData_boundaries T (p+(r,r-1)) ((r-1).toNat+1) _).symm


private theorem towerD_kernel (T : RawTower C) (r : ℤ) (p : ℤ × ℤ)
    (hr : 1 ≤ r) :
    let n := (r - 1).toNat
    kernelSubobject (towerD T r p) =
      imageSubobject (Subobject.ofLE
        ((towerSSData T p).Z ↑(n + 1)) ((towerSSData T p).Z ↑n)
        ((towerSSData T p).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (towerSSData T p).pageπ ↑n) := by
  apply support_kernel_of_representative (towerSSData T p)
    (towerSSData T (p+(r,r-1))) (r-1).toNat (towerD T r p)
  intro z
  rw [towerD_pageπ T r hr p, differentialValue_eq_zero_iff T r hr p]
  exact (towerSSData_cycles T p ((r-1).toNat+1) _).symm

private theorem towerD_image (T : RawTower C) (r : ℤ) (p : ℤ × ℤ)
    (hr : 1 ≤ r) :
    let n := (r - 1).toNat
    let D := towerSSData T (p + (r,r-1))
    imageSubobject (towerD T r p) =
      imageSubobject (Subobject.ofLE (D.B ↑(n + 1)) (D.Z ↑n)
        (le_trans (D.B_le_Z ↑(n + 1))
          (D.Z_anti (by exact_mod_cast Nat.le_succ n))) ≫ D.pageπ ↑n) := by
  exact support_towerD_image T r p hr

private noncomputable def towerSequence (T : RawTower C) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  toPreSS := towerPreSS T
  d_comp_d := towerD_comp T
  Z_succ := towerD_kernel T
  B_succ := towerD_image T


end
end KIP126.Literature.BocksteinRaw

end

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
set_option Elab.async false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private def rawTowerOfSequence (A : ℕ → Syn) (d : ∀ n, A (n+1) ⟶ A n) : RawTower Syn where
  stage := A
  map {s t} h := (Functor.ofOpSequence d).map (homOfLE h).op
  map_self s := (Functor.ofOpSequence d).map_id (Opposite.op s)
  map_comp hrs hst := by
    rw [← Functor.map_comp]
    rfl

private theorem rawTowerOfSequence_succ (A : ℕ → Syn) (d : ∀ n, A (n+1) ⟶ A n)
    (n : ℕ) : (rawTowerOfSequence A d).map (Nat.le_succ n) = d n := by
  exact Functor.ofOpSequence_map_homOfLE_succ d n

private def lambdaTowerStage (X : Syn) (n : ℕ) : Syn :=
  (SyntheticCategory.biShift (lambdaDegree n)).obj X

private def lambdaTowerStep (X : Syn) (n : ℕ) :
    lambdaTowerStage X (n+1) ⟶ lambdaTowerStage X n :=
  lambdaRestrictionSourceMap n (n+1) (Nat.le_succ n) X

private def lambdaTower (X : Syn) : RawTower Syn :=
  rawTowerOfSequence (lambdaTowerStage X) (lambdaTowerStep X)

private theorem lambdaTower_succ (X : Syn) (n : ℕ) :
    (lambdaTower X).map (Nat.le_succ n) = lambdaTowerStep X n :=
  rawTowerOfSequence_succ _ _ n

private theorem lambdaTower_projection (coh : BiShiftCoherence Syn) (X : Syn) (n : ℕ) :
    (lambdaTower X).map (Nat.zero_le n) ≫
      SyntheticCategory.biShift_zero.hom.app X = lambdaPow n X := by
  induction n with
  | zero =>
    rw [RawTower.map_self, Category.id_comp]
    rfl
  | succ n ih =>
    rw [← (lambdaTower X).map_comp (Nat.zero_le n) (Nat.le_succ n),
      Category.assoc, ih, lambdaTower_succ]
    exact lambdaRestrictionSourceMap_commutes coh n (n+1) (Nat.le_succ n) X

private def lambdaRawSequence (X : Syn) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) :=
  towerSequence (lambdaTower X)

private theorem lambdaRawSequence_first (X : Syn) : (lambdaRawSequence X).r₀ = 1 := rfl
private theorem lambdaRawSequence_degree (X : Syn) (r : ℤ) :
    (lambdaRawSequence X).diffDeg r = (r,r-1) := rfl

attribute [local irreducible] lambdaRawSequence

private def lambdaGrading (p : ℤ × ℤ × ℤ) : ℤ × ℤ :=
  (p.2.1-p.2.2, 2*p.2.1-p.1-p.2.2)

private theorem lambdaGrading_add (p : ℤ × ℤ × ℤ) (r : ℤ) :
    lambdaGrading (p + (r,r-1,0)) = lambdaGrading p + (r-1,r-1-1) := by
  rcases p with ⟨s,t,w⟩
  dsimp [lambdaGrading]
  ext <;> dsimp <;> omega

private def lambdaSequenceData (X : Syn) (p : ℤ × ℤ × ℤ) : SSData (ModuleCat.{v} ℤ) :=
  (lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)).ssData
    (lambdaGrading p)

private def lambdaSequenceDifferential (X : Syn) (r : ℤ) (p : ℤ × ℤ × ℤ) :
    (lambdaSequenceData X p).page (↑(r-2).toNat : WithTop ℕ) ⟶
      (lambdaSequenceData X (p+(r,r-1,0))).page (↑(r-2).toNat : WithTop ℕ) := by
  have hp : (p+(r,r-1,0)).2.2 = p.2.2 := by simp
  have hn : r-1-1 = r-2 := by omega
  simpa only [lambdaSequenceData, lambdaRawSequence_first, hp,
    lambdaRawSequence_degree, hn, lambdaGrading_add] using
      (lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)).d
        (r-1) (lambdaGrading p)

private def lambdaPreSequence (X : Syn) : PreSS (ModuleCat.{v} ℤ) (ℤ × ℤ × ℤ) where
  r₀ := 2
  ssData := lambdaSequenceData X
  diffDeg r := (r,r-1,0)
  d := lambdaSequenceDifferential X



private theorem eqMp_heq' {α β : Sort u} (h : α=β) (x : α) : HEq (Eq.mp h x) x := by
  cases h
  rfl
private theorem eqMpr_heq' {α β : Sort u} (h : β=α) (x : α) : HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem lambdaSequenceDifferential_heq (X : Syn) (r : ℤ) (p : ℤ × ℤ × ℤ) :
    HEq (lambdaSequenceDifferential X r p)
      ((lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)).d
        (r-1) (lambdaGrading p)) := by
  unfold lambdaSequenceDifferential
  exact (eqMpr_heq' _ _).trans (eqMp_heq' _ _)


private theorem lambdaPage_eq (X : Syn) (r : ℤ) (p : ℤ × ℤ × ℤ) :
    (lambdaSequenceData X p).page (↑(r-2).toNat : WithTop ℕ) =
      (lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)).Page
        (r-1) (lambdaGrading p) := by
  have hn : r-1-1=r-2 := by omega
  simp only [KIP126.Core.SpectralSequence.Page, lambdaSequenceData, lambdaRawSequence_first, hn]


private theorem composition_zero_of_heq {D : Type*} [Category D] [HasZeroMorphisms D]
    {A B C A' B' C' : D}
    (eA : A=A') (eB : B=B') (eC : C=C')
    {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    (hf : HEq f f') (hg : HEq g g') (h : f' ≫ g' = 0) : f ≫ g = 0 := by
  subst A'; subst B'; subst C'
  cases hf; cases hg
  exact h

private theorem dependent_apply_heq {α : Sort*} {β : α → Sort*}
    (f : (i : α) → β i) {i j : α} (h : i=j) : HEq (f i) (f j) := by
  cases h
  rfl

private theorem lambdaTargetPosition (p : ℤ × ℤ × ℤ) (r : ℤ) :
    ((p+(r,r-1,0)).2.2, lambdaGrading (p+(r,r-1,0))) =
      (p.2.2, lambdaGrading p+(r-1,r-1-1)) := by
  apply Prod.ext
  · simp
  · exact lambdaGrading_add p r

private theorem lambdaTargetPage_eq (X : Syn) (r : ℤ) (p : ℤ × ℤ × ℤ) :
    (lambdaSequenceData X (p+(r,r-1,0))).page (↑(r-2).toNat : WithTop ℕ) =
      (lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)).Page
        (r-1) (lambdaGrading p+(r-1,r-1-1)) := by
  refine (lambdaPage_eq X r (p+(r,r-1,0))).trans ?_
  have h := congrArg (fun q : ℤ × (ℤ × ℤ) =>
    (lambdaRawSequence ((SyntheticCategory.biShift (0,-q.1)).obj X)).Page (r-1) q.2)
      (lambdaTargetPosition p r)
  dsimp only at h
  exact h

private theorem lambdaSequenceDifferential_comp (X : Syn) (r : ℤ) (p : ℤ × ℤ × ℤ) :
    lambdaSequenceDifferential X r p ≫ lambdaSequenceDifferential X r (p+(r,r-1,0)) = 0 := by
  let E := lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)
  have hd1 : HEq (lambdaSequenceDifferential X r (p+(r,r-1,0)))
      (E.d (r-1) (lambdaGrading p + E.diffDeg (r-1))) := by
    refine (lambdaSequenceDifferential_heq X r (p+(r,r-1,0))).trans ?_
    have hp : ((p+(r,r-1,0)).2.2, lambdaGrading (p+(r,r-1,0))) =
        (p.2.2, lambdaGrading p+E.diffDeg (r-1)) := by
      simpa only [E, lambdaRawSequence_degree] using lambdaTargetPosition p r
    have h := dependent_apply_heq (fun q : ℤ × (ℤ × ℤ) =>
      (lambdaRawSequence ((SyntheticCategory.biShift (0,-q.1)).obj X)).d (r-1) q.2) hp
    dsimp only at h
    exact h
  have hC : (lambdaSequenceData X ((p+(r,r-1,0))+(r,r-1,0))).page (↑(r-2).toNat : WithTop ℕ) =
      E.Page (r-1) ((lambdaGrading p + E.diffDeg (r-1)) + E.diffDeg (r-1)) := by
    refine (lambdaTargetPage_eq X r (p+(r,r-1,0))).trans ?_
    simp only [E, lambdaRawSequence_degree]
    have h := congrArg (fun q : ℤ × (ℤ × ℤ) =>
      (lambdaRawSequence ((SyntheticCategory.biShift (0,-q.1)).obj X)).Page
        (r-1) (q.2+(r-1,r-1-1))) (lambdaTargetPosition p r)
    dsimp only at h
    exact h
  have hB : (lambdaSequenceData X (p+(r,r-1,0))).page (↑(r-2).toNat : WithTop ℕ) =
      E.Page (r-1) (lambdaGrading p+E.diffDeg (r-1)) := by
    simpa only [E, lambdaRawSequence_degree] using lambdaTargetPage_eq X r p
  exact composition_zero_of_heq (lambdaPage_eq X r p) hB hC
    (lambdaSequenceDifferential_heq X r p) hd1 (E.d_comp_d (r-1) (lambdaGrading p))


private theorem kernel_eq_of_heq {D : Type*} [Category D] [Abelian D]
    {A B A' B' : D} (eA : A=A') (eB : B=B')
    {f : A ⟶ B} {f' : A' ⟶ B'} {K : Subobject A} {K' : Subobject A'}
    (hf : HEq f f') (hK : HEq K K') (h : kernelSubobject f' = K') :
    kernelSubobject f = K := by
  subst A'; subst B'
  cases hf; cases hK
  exact h

private theorem image_eq_of_heq {D : Type*} [Category D] [Abelian D]
    {A B A' B' : D} (eA : A=A') (eB : B=B')
    {f : A ⟶ B} {f' : A' ⟶ B'} {K : Subobject B} {K' : Subobject B'}
    (hf : HEq f f') (hK : HEq K K') (h : imageSubobject f' = K') :
    imageSubobject f = K := by
  subst A'; subst B'
  cases hf; cases hK
  exact h


private def cycleSuccessorImage (D : SSData (ModuleCat.{v} ℤ)) (n : ℕ) :
    Subobject (D.page ↑n) :=
  imageSubobject (Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n)
    (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ D.pageπ ↑n)

private def boundarySuccessorImage (D : SSData (ModuleCat.{v} ℤ)) (n : ℕ) :
    Subobject (D.page ↑n) :=
  imageSubobject (Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑n)
    (le_trans (D.B_le_Z ↑(n+1))
      (D.Z_anti (by exact_mod_cast Nat.le_succ n))) ≫ D.pageπ ↑n)

private theorem lambdaTargetData_eq (X : Syn) (r : ℤ) (p : ℤ × ℤ × ℤ) :
    lambdaSequenceData X (p+(r,r-1,0)) =
      (lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)).ssData
        (lambdaGrading p+(r-1,r-1-1)) := by
  have h := congrArg (fun q : ℤ × (ℤ × ℤ) =>
    (lambdaRawSequence ((SyntheticCategory.biShift (0,-q.1)).obj X)).ssData q.2)
      (lambdaTargetPosition p r)
  dsimp only at h
  exact h

private def lambdaSequence (X : Syn) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ × ℤ) where
  toPreSS := lambdaPreSequence X
  d_comp_d := lambdaSequenceDifferential_comp X
  Z_succ r p hr := by
    let E := lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)
    have hn : (r-1-E.r₀).toNat = (r-2).toNat := by
      rw [show E.r₀=1 from lambdaRawSequence_first _]
      congr 1
      omega
    have h := E.Z_succ (r-1) (lambdaGrading p) (by
      rw [show E.r₀=1 from lambdaRawSequence_first _]
      change 2 ≤ r at hr
      omega)
    refine kernel_eq_of_heq (lambdaPage_eq X r p) ?_
      (lambdaSequenceDifferential_heq X r p) ?_ h
    · simpa only [E, lambdaRawSequence_degree, lambdaPreSequence,
        KIP126.Core.SpectralSequence.Page] using lambdaTargetPage_eq X r p
    · change HEq (cycleSuccessorImage (E.ssData (lambdaGrading p)) (r-2).toNat)
        (cycleSuccessorImage (E.ssData (lambdaGrading p)) (r-1-E.r₀).toNat)
      exact dependent_apply_heq (cycleSuccessorImage (E.ssData (lambdaGrading p))) hn.symm
  B_succ r p hr := by
    let E := lambdaRawSequence ((SyntheticCategory.biShift (0,-p.2.2)).obj X)
    have hn : (r-1-E.r₀).toNat = (r-2).toNat := by
      rw [show E.r₀=1 from lambdaRawSequence_first _]
      congr 1
      omega
    have h := E.B_succ (r-1) (lambdaGrading p) (by
      rw [show E.r₀=1 from lambdaRawSequence_first _]
      change 2 ≤ r at hr
      omega)
    refine image_eq_of_heq (lambdaPage_eq X r p) ?_
      (lambdaSequenceDifferential_heq X r p) ?_ h
    · simpa only [E, lambdaRawSequence_degree, lambdaPreSequence,
        KIP126.Core.SpectralSequence.Page] using lambdaTargetPage_eq X r p
    · change HEq (boundarySuccessorImage (lambdaSequenceData X (p+(r,r-1,0))) (r-2).toNat)
        (boundarySuccessorImage (E.ssData (lambdaGrading p+E.diffDeg (r-1))) (r-1-E.r₀).toNat)
      have hD : lambdaSequenceData X (p+(r,r-1,0)) =
          E.ssData (lambdaGrading p+E.diffDeg (r-1)) := by
        simpa only [E, lambdaRawSequence_degree] using lambdaTargetData_eq X r p
      have hpair : (lambdaSequenceData X (p+(r,r-1,0)), (r-2).toNat) =
          (E.ssData (lambdaGrading p+E.diffDeg (r-1)), (r-1-E.r₀).toNat) :=
        Prod.ext hD hn.symm
      have hh := dependent_apply_heq
        (fun q : SSData (ModuleCat.{v} ℤ) × ℕ => boundarySuccessorImage q.1 q.2) hpair
      dsimp only at hh
      exact hh

private theorem lambdaSequence_first (X : Syn) : (lambdaSequence X).r₀ = 2 := rfl
private theorem lambdaSequence_degree (X : Syn) (r : ℤ) :
    (lambdaSequence X).diffDeg r = (r,r-1,0) := rfl

end
end KIP126.Literature.BocksteinRaw

end

/-! Initial-page comparisons for the quotient triangles and the
negative-filtration support bound. -/

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
private theorem rawMapAt_eqToHom (T : RawTower C) {s t : ℤ} (h : s ≤ t) (hst : s=t) :
    T.mapAt h = eqToHom (by rw [hst]) := by
  subst t
  exact T.map_self _

private theorem rawCycles_one (T : RawTower C) (p : ℤ × ℤ) :
    T.cycles 1 (by decide) p = ⊤ := by
  apply top_unique
  intro x hx
  refine ⟨T.connecting p x, ?_⟩
  change T.connecting p x ≫ T.mapAt (show p.1+1 ≤ p.1+(1:ℕ) by omega) = _
  rw [rawMapAt_eqToHom T _ (by omega)]
  exact Category.comp_id _

private theorem rawBoundaries_one (T : RawTower C) (p : ℤ × ℤ) :
    T.boundaries 1 (by decide) p = ⊥ := by
  apply bot_unique
  rintro x ⟨y,hy,hx⟩
  let f := T.mapAt (show p.1-(1:ℕ)+1 ≤ p.1 by omega)
  have hf : IsIso f := by
    dsimp only [f]
    rw [rawMapAt_eqToHom T _ (by omega)]
    infer_instance
  have hy0 : y=0 := by
    apply (cancel_mono f).mp
    change y ≫ f = 0 ≫ f
    change y ≫ f = 0 at hy
    simpa only [zero_comp] using hy
  change x=0
  rw [← hx, hy0, map_zero]

private theorem rawFiniteBoundaries_zero (T : RawTower C) (p : ℤ × ℤ) :
    finiteBoundaries T p 0 = ⊥ := by
  change (T.boundaries 1 (by decide) p).comap (T.cycles 1 (by decide) p).subtype = ⊥
  rw [rawBoundaries_one]
  ext x
  change (x.val = 0) ↔ x=0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem rawData_B_zero (T : RawTower C) (p : ℤ × ℤ) :
    (towerSSData T p).B 0 = ⊥ := by
  change (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm
    (finiteBoundaries T p 0) = ⊥
  rw [rawFiniteBoundaries_zero, OrderIso.map_bot]

private def rawAmbientIso (T : RawTower C) (p : ℤ × ℤ) :
    (towerSSData T p).V ≅ ModuleCat.of ℤ (T.FirstPage p) :=
  (LinearEquiv.ofBijective (T.cycles 1 (by decide) p).subtype ⟨
    Subtype.val_injective, fun x => ⟨⟨x, by rw [rawCycles_one]; trivial⟩, rfl⟩⟩).toModuleIso

private theorem rawPageProjection_isIso (T : RawTower C) (p : ℤ × ℤ) :
    IsIso ((towerSSData T p).pageπ 0) := by
  let D := towerSSData T p
  have hzero : Subobject.ofLE (D.B 0) (D.Z 0) (D.B_le_Z 0) = 0 := by
    apply (cancel_mono (D.Z 0).arrow).mp
    rw [Subobject.ofLE_arrow, zero_comp, show D.B 0 = ⊥ from rawData_B_zero T p,
      Subobject.bot_arrow]
  change IsIso (cokernel.π (Subobject.ofLE (D.B 0) (D.Z 0) (D.B_le_Z 0)))
  rw [hzero]
  exact cokernel.π_zero_isIso

private def rawFirstPageIso (T : RawTower C) (p : ℤ × ℤ) :
    (towerSequence T).Page 1 p ≅ ModuleCat.of ℤ (T.FirstPage p) := by
  let D := towerSSData T p
  have hp : IsIso (D.pageπ 0) := rawPageProjection_isIso T p
  have hz : IsIso (D.Z 0).arrow := by
    rw [D.Z_zero]
    infer_instance
  exact (asIso (D.pageπ 0)).symm ≪≫ asIso (D.Z 0).arrow ≪≫ rawAmbientIso T p
end
end KIP126.Literature.BocksteinRaw

end

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private def lambdaStepTriangle (X : Syn) (k : ℕ) : Triangle Syn :=
  Triangle.mk (lambdaTowerStep X k) (HasFunctorialCofiber.cofibι (lambdaTowerStep X k))
    (HasFunctorialCofiber.cofibδ (lambdaTowerStep X k))

private def lambdaStepTriangleIso (X : Syn) (k : ℕ)
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).IsTriangulated] :
    lambdaStepTriangle X k ≅
      (SyntheticCategory.biShift (lambdaDegree k)).mapTriangle.obj
        (XModLambdaN.cofiberTriangle X 1) := by
  let F := SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)
  refine isoTriangleOfIso₁₂ _ _
    (HasFunctorialCofiber.cofib_distinguished (lambdaTowerStep X k))
    (F.map_distinguished _ (XModLambdaN.cofiberTriangle_distinguished X 1))
    ((lambdaShiftAddIso 1 k (k+1) (by omega)).symm.app X) (Iso.refl _) ?_
  change lambdaTowerStep X k ≫ 𝟙 _ =
    (lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X ≫ F.map (lambdaPow 1 X)
  rw [Category.comp_id]
  have h (n : ℕ) (hn : n+k=k+1) :
      (lambdaShiftAddIso n k (k+1) hn).inv.app X ≫ F.map (lambdaPow n X) =
        (lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X ≫ F.map (lambdaPow 1 X) := by
    have h1 : n=1 := by omega
    subst n
    rfl
  exact h (k+1-k) (by omega)

private def lambdaStepLayerIso (X : Syn) (k : ℕ)
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).IsTriangulated] :
    HasFunctorialCofiber.cofib (lambdaTowerStep X k) ≅
      (SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN X 1) :=
  Triangle.π₃.mapIso (lambdaStepTriangleIso X k)

private theorem lambdaStepLayerIso_incl (X : Syn) (k : ℕ)
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).IsTriangulated] :
    HasFunctorialCofiber.cofibι (lambdaTowerStep X k) ≫ (lambdaStepLayerIso X k).hom =
      (SyntheticCategory.biShift (lambdaDegree k)).map (XModLambdaN.incl X 1) := by
  have h := (lambdaStepTriangleIso X k).hom.comm₂
  change HasFunctorialCofiber.cofibι (lambdaTowerStep X k) ≫
    (lambdaStepLayerIso X k).hom =
      (lambdaStepTriangleIso X k).hom.hom₂ ≫
        (SyntheticCategory.biShift (lambdaDegree k)).map (XModLambdaN.incl X 1) at h
  have h2 : (lambdaStepTriangleIso X k).hom.hom₂ = 𝟙 _ := by
    simp [lambdaStepTriangleIso]
  rw [h2, Category.id_comp] at h
  exact h
private theorem lambdaStepLayerIso_boundary (X : Syn) (k : ℕ)
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).IsTriangulated] :
    HasFunctorialCofiber.cofibδ (lambdaTowerStep X k) ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X) =
      (lambdaStepLayerIso X k).hom ≫
        (SyntheticCategory.biShift (lambdaDegree k)).map (XModLambdaN.proj X 1) ≫
        ((SyntheticCategory.biShift (lambdaDegree k)).commShiftIso (1 : ℤ)).hom.app
          ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) := by
  have h := (lambdaStepTriangleIso X k).hom.comm₃
  change HasFunctorialCofiber.cofibδ (lambdaTowerStep X k) ≫
      (shiftFunctor Syn (1 : ℤ)).map ((lambdaStepTriangleIso X k).hom.hom₁) =
    (lambdaStepLayerIso X k).hom ≫
      (SyntheticCategory.biShift (lambdaDegree k)).map (XModLambdaN.proj X 1) ≫
      ((SyntheticCategory.biShift (lambdaDegree k)).commShiftIso (1 : ℤ)).hom.app
        ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) at h
  have h1 : (lambdaStepTriangleIso X k).hom.hom₁ =
      (lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X := by
    simp [lambdaStepTriangleIso]
  rw [h1] at h
  exact h

private theorem lambdaLayer_nat (X : Syn) (k : ℕ) :
    (lambdaTower X).layer (k : ℤ) = HasFunctorialCofiber.cofib (lambdaTowerStep X k) := by
  change HasFunctorialCofiber.cofib ((lambdaTower X).map (Nat.le_succ k)) = _
  rw [lambdaTower_succ]

private def lambdaLayerIso (X : Syn) (k : ℕ)
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).IsTriangulated] :
    (lambdaTower X).layer (k : ℤ) ≅
      (SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN X 1) :=
  eqToIso (lambdaLayer_nat X k) ≪≫ lambdaStepLayerIso X k

end
end KIP126.Literature.BocksteinRaw

end

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private theorem rawMap_isIso_of_eq (T : RawTower Syn) {i j : ℕ}
    (h : i ≤ j) (hij : i=j) : IsIso (T.map h) := by
  subst j
  rw [T.map_self]
  infer_instance

private theorem rawLayer_isZero_negative (T : RawTower Syn) (k : ℤ) (hk : k<0) :
    IsZero (T.layer k) := by
  let f := T.mapAt (show k ≤ k+1 by omega)
  have hf : IsIso f := rawMap_isIso_of_eq T _ (by omega)
  exact Triangle.isZero₃_of_isIso₁ _ (HasFunctorialCofiber.cofib_distinguished f) hf

private theorem rawPage_isZero_negative (T : RawTower Syn) (r : ℤ) (p : ℤ × ℤ)
    (hp : p.1<0) : IsZero ((towerSequence T).Page r p) := by
  have hL := rawLayer_isZero_negative T p.1 hp
  haveI : Subsingleton (T.FirstPage p) := ⟨fun a b => hL.eq_of_tgt a b⟩
  have hV : IsZero (towerSSData T p).V :=
    (rawAmbientIso T p).isZero_iff.mpr (ModuleCat.isZero_of_subsingleton _)
  let n : WithTop ℕ := ↑(r-(towerSequence T).r₀).toNat
  haveI : Epi ((towerSSData T p).pageπ n) := by
    change Epi (cokernel.π _)
    infer_instance
  exact IsZero.of_epi ((towerSSData T p).pageπ n)
    (IsZero.of_mono ((towerSSData T p).Z n).arrow hV)

private theorem lambdaPage_isZero_negative (X : Syn) (r : ℤ) (p : ℤ × ℤ × ℤ)
    (hp : p.2.1<p.2.2) : IsZero ((lambdaSequence X).Page r p) := by
  apply (eqToIso (lambdaPage_eq X r p)).isZero_iff.mpr
  exact rawPage_isZero_negative _ _ _ (by dsimp [lambdaGrading]; omega)

private def homotopyModuleIso {A B : Syn} (e : A ≅ B) (m : ℤ) :
    ModuleCat.of ℤ (HomotopyGroup m A) ≅ ModuleCat.of ℤ (HomotopyGroup m B) :=
  (LinearEquiv.ofBijective (inducedMap e.hom m).toIntLinearMap ⟨
    fun a b h => (cancel_mono e.hom).mp h,
    fun b => ⟨b ≫ e.inv, by change (b ≫ e.inv) ≫ e.hom = b; simp⟩⟩).toModuleIso

private def lambdaFirstPageIso (X : Syn) (p : ℤ × ℤ × ℤ) (k : ℕ)
    (hk : p.2.1-p.2.2 = (k : ℤ))
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).IsTriangulated] :
    (lambdaSequence X).Page 2 p ≅
      ModuleCat.of ℤ (HomotopyGroup (p.2.1-p.1)
        ((SyntheticCategory.biShift (lambdaDegree k)).obj
          (XModLambdaN ((SyntheticCategory.biShift (0,-p.2.2)).obj X) 1))) := by
  let Y := (SyntheticCategory.biShift (0,-p.2.2)).obj X
  have hgrade : lambdaGrading p = ((k : ℤ), p.2.1-p.1+k) := by
    ext <;> dsimp [lambdaGrading] <;> omega
  refine eqToIso (lambdaPage_eq X 2 p) ≪≫
    eqToIso (congrArg ((lambdaRawSequence Y).Page 1) hgrade) ≪≫
    rawFirstPageIso (lambdaTower Y) ((k : ℤ), p.2.1-p.1+k) ≪≫
    homotopyModuleIso (lambdaLayerIso Y k) (p.2.1-p.1+k-k) ≪≫ ?_
  exact eqToIso (congrArg (fun m : ℤ => ModuleCat.of ℤ (HomotopyGroup m
    ((SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN Y 1))))
      (show p.2.1-p.1+k-k = p.2.1-p.1 by omega))
end
end KIP126.Literature.BocksteinRaw
end

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private def lambdaOneShiftSourceIso (a : ℤ × ℤ) (X : Syn) :
    (SyntheticCategory.biShift (lambdaDegree 1)).obj ((SyntheticCategory.biShift a).obj X) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) :=
  (biShiftAddIso a (0,-1) (a+(0,-1)) rfl).app X ≪≫
    ((biShiftAddIso (0,-1) a (a+(0,-1)) (add_comm _ _)).symm.app X)

private def lambdaOneShiftTriangleIso (coh : BiShiftCoherence Syn) (a : ℤ × ℤ) (X : Syn)
    [(SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    XModLambdaN.cofiberTriangle ((SyntheticCategory.biShift a).obj X) 1 ≅
      (SyntheticCategory.biShift a).mapTriangle.obj (XModLambdaN.cofiberTriangle X 1) := by
  let F := SyntheticCategory.biShift (Syn := Syn) a
  refine isoTriangleOfIso₁₂ _ _
    (XModLambdaN.cofiberTriangle_distinguished _ 1)
    (F.map_distinguished _ (XModLambdaN.cofiberTriangle_distinguished X 1))
    (lambdaOneShiftSourceIso a X) (Iso.refl _) ?_
  change lambdaPow 1 (F.obj X) ≫ 𝟙 _ = (lambdaOneShiftSourceIso a X).hom ≫ F.map (lambdaPow 1 X)
  rw [Category.comp_id, lambdaPow_one coh, lambdaPow_one coh]
  simpa [F, lambdaOneShiftSourceIso, Category.assoc] using coh.lambda_comm a X

private def lambdaOneShiftIso (coh : BiShiftCoherence Syn) (a : ℤ × ℤ) (X : Syn)
    [(SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    XModLambdaN ((SyntheticCategory.biShift a).obj X) 1 ≅
      (SyntheticCategory.biShift a).obj (XModLambdaN X 1) :=
  Triangle.π₃.mapIso (lambdaOneShiftTriangleIso coh a X)

private def lambdaFirstLayerNormalizedIso (coh : BiShiftCoherence Syn) (X : Syn)
    (w t : ℤ) (k : ℕ) (hk : t-w=(k : ℤ))
    [(SyntheticCategory.biShift (Syn := Syn) (0,-w)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (0,-w)).IsTriangulated] :
    (SyntheticCategory.biShift (lambdaDegree k)).obj
        (XModLambdaN ((SyntheticCategory.biShift (0,-w)).obj X) 1) ≅
      (SyntheticCategory.biShift (0,-t)).obj (XModLambdaN X 1) :=
  (SyntheticCategory.biShift (lambdaDegree k)).mapIso (lambdaOneShiftIso coh (0,-w) X) ≪≫
    (biShiftAddIso (0,-w) (lambdaDegree k) (0,-t) (by
      ext <;> dsimp [lambdaDegree] <;> omega)).app (XModLambdaN X 1)

private def homotopyBiHomZeroEquiv (Y : Syn) (m : ℤ) : HomotopyGroup m Y ≃+ BiHom m 0 Y where
  toFun f := (SyntheticCategory.biShift_compat (Syn := Syn) m).hom.app S_0_0 ≫ f
  invFun f := (SyntheticCategory.biShift_compat (Syn := Syn) m).inv.app S_0_0 ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.comp_add]

private def biHomWeightShiftEquiv (X : Syn) (m w : ℤ)
    [(SyntheticCategory.biShift (Syn := Syn) (0,-w)).Additive] :
    BiHom m w X ≃+ BiHom m 0 ((SyntheticCategory.biShift (0,-w)).obj X) where
  toEquiv := (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-w)).homEquiv.trans
    (Iso.homCongr ((biShiftAddIso (m,w) (0,-w) (m,0) (by ext <;> simp)).app S_0_0)
      (Iso.refl _))
  map_add' f g := by
    change (biShiftAddIso (m,w) (0,-w) (m,0) (by ext <;> simp)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (0,-w)).map (f+g) ≫ 𝟙 _ =
      ((biShiftAddIso (m,w) (0,-w) (m,0) (by ext <;> simp)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (0,-w)).map f ≫ 𝟙 _) +
      ((biShiftAddIso (m,w) (0,-w) (m,0) (by ext <;> simp)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (0,-w)).map g ≫ 𝟙 _)
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

private def lambdaInitialQuotientIso (coh : BiShiftCoherence Syn)
    (X : Syn) (p : ℤ × ℤ × ℤ) (k : ℕ) (hk : p.2.1-p.2.2 = (k : ℤ))
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).IsTriangulated]
    [(SyntheticCategory.biShift (Syn := Syn) (0,-p.2.2)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) (0,-p.2.2)).IsTriangulated]
    [(SyntheticCategory.biShift (Syn := Syn) (0,-p.2.1)).Additive] :
    (lambdaSequence X).Page 2 p ≅ ModuleCat.of ℤ (BiHom (p.2.1-p.1) p.2.1 (XModLambdaN X 1)) :=
  lambdaFirstPageIso X p k hk ≪≫
    homotopyModuleIso (lambdaFirstLayerNormalizedIso coh X p.2.2 p.2.1 k hk) (p.2.1-p.1) ≪≫
    ((homotopyBiHomZeroEquiv _ (p.2.1-p.1)).trans
      (biHomWeightShiftEquiv (XModLambdaN X 1) (p.2.1-p.1) p.2.1).symm).toIntLinearEquiv.toModuleIso
end
end KIP126.Literature.BocksteinRaw
end
