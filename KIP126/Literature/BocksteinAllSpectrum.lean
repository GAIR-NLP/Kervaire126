module
import all KIP126.Literature.BocksteinLambdaCycles
import all KIP126.Literature.BocksteinFiniteQuotientShift
import all KIP126.Literature.BocksteinComparisonInput
import all KIP126.Literature.BocksteinBoundaryInput

@[expose] section
namespace KIP126.Literature.Paper38AllSpectrum
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core KIP126.Core.SpectralSequence
open KIP126.Literature.BocksteinRaw
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private theorem restrictionSource_shift (coh : BiShiftCoherence Syn)
    (b : ℤ × ℤ) (i j : ℕ) (hij : i ≤ j) (X : Syn) :
    lambdaRestrictionSourceMap i j hij ((SyntheticCategory.biShift b).obj X) ≫
        (lambdaFiniteShiftSourceIso b i X).hom =
      (lambdaFiniteShiftSourceIso b j X).hom ≫
        (SyntheticCategory.biShift b).map (lambdaRestrictionSourceMap i j hij X) := by
  apply (cancel_epi ((lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).hom.app
    ((SyntheticCategory.biShift b).obj X))).mp
  change (lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).hom.app
      ((SyntheticCategory.biShift b).obj X) ≫
    ((lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).inv.app
      ((SyntheticCategory.biShift b).obj X) ≫
      (SyntheticCategory.biShift (lambdaDegree i)).map
        (lambdaPow (j-i) ((SyntheticCategory.biShift b).obj X))) ≫
      (biShiftSwapIso b (lambdaDegree i) X).hom = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [lambdaPow_shift coh, Functor.map_comp]
  change ((SyntheticCategory.biShift (lambdaDegree i)).map
      (biShiftSwapIso b (lambdaDegree (j-i)) X).hom ≫
      (SyntheticCategory.biShift (lambdaDegree i)).map
        ((SyntheticCategory.biShift b).map (lambdaPow (j-i) X))) ≫
        (biShiftSwapIso b (lambdaDegree i) X).hom = _
  rw [Category.assoc, biShiftSwap_naturality]
  have hhex := biShiftSwap_hexagon coh b (lambdaDegree (j-i)) (lambdaDegree i)
    (lambdaDegree j) (by ext <;> simp [lambdaDegree]; omega) X
  change _ = (lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).hom.app
      ((SyntheticCategory.biShift b).obj X) ≫
    (biShiftSwapIso b (lambdaDegree j) X).hom ≫
      (SyntheticCategory.biShift b).map
        ((lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).inv.app X ≫
          (SyntheticCategory.biShift (lambdaDegree i)).map (lambdaPow (j-i) X))
  have hhex' := congrArg (fun f => f ≫ (SyntheticCategory.biShift b).map
      ((lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).inv.app X ≫
        (SyntheticCategory.biShift (lambdaDegree i)).map (lambdaPow (j-i) X))) hhex
  simp only [lambdaShiftAddIso, Functor.map_comp, Category.assoc] at hhex'
  have hc : (SyntheticCategory.biShift b).map
      ((lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).hom.app X) ≫
      (SyntheticCategory.biShift b).map
        ((lambdaShiftAddIso (j-i) i j (Nat.sub_add_cancel hij)).inv.app X) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [lambdaShiftAddIso] at hc
  rw [← Category.assoc ((SyntheticCategory.biShift b).map
      ((biShiftAddIso (lambdaDegree (j-i)) (lambdaDegree i) (lambdaDegree j) _).hom.app X)),
      hc, Category.id_comp] at hhex'
  simpa only [lambdaShiftAddIso, Functor.map_comp, Category.assoc] using hhex'.symm

variable [HasFunctorialCofiber (C := Syn)]

private theorem restriction_range (coh : BiShiftCoherence Syn)
    (X : Syn) (i j : ℕ) (hij : i ≤ j) {P : Syn} (x : P ⟶ XModLambdaN X i) :
    (∃ z : P ⟶ XModLambdaN X j, z ≫ XModLambdaN.restriction coh X i j hij = x) ↔
      ∃ a : P ⟶ ((SyntheticCategory.biShift (lambdaDegree j)).obj X)⟦(1:ℤ)⟧,
        x ≫ XModLambdaN.proj X i =
          a ≫ (shiftFunctor Syn (1:ℤ)).map (lambdaRestrictionSourceMap i j hij X) := by
  have h := lambdaRestriction_shift_range coh X i j hij (𝟭 Syn) x
  simp only [Functor.id_obj, Functor.id_map, Functor.commShiftIso_id_hom_app] at h
  simpa only [lambdaDegree, Category.comp_id] using h

private theorem restriction_shift_range (coh : BiShiftCoherence Syn)
    (b : ℤ × ℤ) (X : Syn) (i j : ℕ) (hij : i ≤ j)
    [(SyntheticCategory.biShift (Syn:=Syn) b).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) b).IsTriangulated]
    {P : Syn} (x : P ⟶ XModLambdaN ((SyntheticCategory.biShift b).obj X) i) :
    (∃ z : P ⟶ XModLambdaN ((SyntheticCategory.biShift b).obj X) j,
      z ≫ XModLambdaN.restriction coh ((SyntheticCategory.biShift b).obj X) i j hij = x) ↔
      ∃ z : P ⟶ (SyntheticCategory.biShift b).obj (XModLambdaN X j),
        z ≫ (SyntheticCategory.biShift b).map (XModLambdaN.restriction coh X i j hij) =
          x ≫ (lambdaFiniteShiftIso coh b i X).hom := by
  rw [restriction_range, lambdaRestriction_shift_range]
  let eA := (shiftFunctor Syn (1:ℤ)).mapIso (lambdaFiniteShiftSourceIso b j X)
  let eB := (shiftFunctor Syn (1:ℤ)).mapIso (lambdaFiniteShiftSourceIso b i X)
  let g := (shiftFunctor Syn (1:ℤ)).map
    (lambdaRestrictionSourceMap i j hij ((SyntheticCategory.biShift b).obj X))
  let g' := (shiftFunctor Syn (1:ℤ)).map
    ((SyntheticCategory.biShift b).map (lambdaRestrictionSourceMap i j hij X))
  have he : g ≫ eB.hom = eA.hom ≫ g' := by
    change (shiftFunctor Syn (1:ℤ)).map _ ≫ (shiftFunctor Syn (1:ℤ)).map _ =
      (shiftFunctor Syn (1:ℤ)).map _ ≫ (shiftFunctor Syn (1:ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp, restrictionSource_shift coh]
  have h := map_range_iff_iso eA eB g g' he (x ≫ XModLambdaN.proj _ i)
  have hb : (x ≫ XModLambdaN.proj ((SyntheticCategory.biShift b).obj X) i) ≫ eB.hom =
      (x ≫ (lambdaFiniteShiftIso coh b i X).hom) ≫
        (SyntheticCategory.biShift b).map (XModLambdaN.proj X i) ≫
        ((SyntheticCategory.biShift b).commShiftIso (1:ℤ)).hom.app
          ((SyntheticCategory.biShift (lambdaDegree i)).obj X) := by
    change (x ≫ XModLambdaN.proj ((SyntheticCategory.biShift b).obj X) i) ≫
      (shiftFunctor Syn (1:ℤ)).map (lambdaFiniteShiftSourceIso b i X).hom = _
    rw [Category.assoc, lambdaFiniteShiftIso_proj coh]
    simp only [Category.assoc]
  rw [hb] at h
  exact h

omit [HasFunctorialCofiber (C := Syn)] in
private theorem zeroShift_range {A B P : Syn} (f : A ⟶ B)
    (x : P ⟶ (SyntheticCategory.biShift (0,0)).obj B) :
    (∃ z : P ⟶ (SyntheticCategory.biShift (0,0)).obj A,
      z ≫ (SyntheticCategory.biShift (0,0)).map f = x) ↔
      ∃ z : P ⟶ A, z ≫ f = x ≫ SyntheticCategory.biShift_zero.hom.app B := by
  have h := map_range_iff_iso (SyntheticCategory.biShift_zero.app A)
    (SyntheticCategory.biShift_zero.app B) ((SyntheticCategory.biShift (0,0)).map f) f
    (SyntheticCategory.biShift_zero.hom.naturality f) x
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨z',hz'⟩ := h.mp ⟨z,hz.symm⟩
    exact ⟨z',hz'.symm⟩
  · rintro ⟨z,hz⟩
    obtain ⟨z',hz'⟩ := h.mpr ⟨z,hz.symm⟩
    exact ⟨z',hz'.symm⟩

private theorem rawFirstPageIso_cycleRep (T : RawTower Syn) (p : ℤ × ℤ) (n : ℕ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z n) : ModuleCat ℤ)) :
    (rawFirstPageIso T p).hom
      ((Subobject.ofLE ((towerSSData T p).Z n) ((towerSSData T p).Z 0)
        ((towerSSData T p).Z_anti (show (0:WithTop ℕ) ≤ n from bot_le)) ≫
        (towerSSData T p).pageπ 0) z) = cycleRep T p n z := by
  let D := towerSSData T p
  let i := Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti (show (0:WithTop ℕ) ≤ n from bot_le))
  letI : IsIso (D.pageπ 0) := rawPageProjection_isIso T p
  have he : D.pageπ 0 ≫ (rawFirstPageIso T p).hom =
      (D.Z 0).arrow ≫ (rawAmbientIso T p).hom := by
    simp only [D, rawFirstPageIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
      IsIso.hom_inv_id_assoc]
  change ((i ≫ D.pageπ 0) ≫ (rawFirstPageIso T p).hom) z = _
  rw [Category.assoc, he, ← Category.assoc, Subobject.ofLE_arrow]
  rfl

private theorem raw_cycles_finiteHom (coh : BiShiftCoherence Syn)
    (Z : Syn) (t m : ℤ) (q : ℕ) (hq : 1 ≤ q)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree 0)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree 0)).IsTriangulated]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-t)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-t)).IsTriangulated]
    (z : (lambdaTower ((SyntheticCategory.biShift (0,-t)).obj Z)).FirstPage (0,m))
    (hz : z ∈ (lambdaTower ((SyntheticCategory.biShift (0,-t)).obj Z)).cycles q hq (0,m)) :
    ∃ a : HomotopyGroup (m-0)
        ((SyntheticCategory.biShift (0,-t)).obj (XModLambdaN Z q)),
      a ≫ (SyntheticCategory.biShift (0,-t)).map (XModLambdaN.restriction coh Z 1 q hq) =
        z ≫ (lambdaLayerIso ((SyntheticCategory.biShift (0,-t)).obj Z) 0).hom ≫
          (lambdaFirstLayerNormalizedIso coh Z t t 0 (by simp)).hom := by
  let Y := (SyntheticCategory.biShift (0,-t)).obj Z
  have h := (lambda_cycles_iff_shifted_restriction coh Y 0 q hq m z).mp hz
  have h' := (zeroShift_range (XModLambdaN.restriction coh Y 1 q hq)
    (z ≫ (lambdaLayerIso Y 0).hom)).mp h
  have h'' := (restriction_shift_range coh (0,-t) Z 1 q hq
    ((z ≫ (lambdaLayerIso Y 0).hom) ≫ SyntheticCategory.biShift_zero.hom.app
      (XModLambdaN Y 1))).mp h'
  have hn : SyntheticCategory.biShift_zero.hom.app (XModLambdaN Y 1) ≫
      (lambdaFiniteShiftIso coh (0,-t) 1 Z).hom =
        (lambdaFirstLayerNormalizedIso coh Z t t 0 (by simp)).hom := by
    rw [lambdaFiniteShiftIso_one]
    change SyntheticCategory.biShift_zero.hom.app (XModLambdaN Y 1) ≫
        (lambdaOneShiftIso coh (0,-t) Z).hom =
      (SyntheticCategory.biShift (0,0)).map (lambdaOneShiftIso coh (0,-t) Z).hom ≫
        (biShiftAddIso (0,-t) 0 (0,-t) (add_zero _)).hom.app (XModLambdaN Z 1)
    rw [coh.right_unit]
    exact (SyntheticCategory.biShift_zero.hom.naturality
      (lambdaOneShiftIso coh (0,-t) Z).hom).symm
  rcases h'' with ⟨a,ha⟩
  refine ⟨a, ?_⟩
  simpa only [Category.assoc, hn] using ha

private theorem raw_cycles_finiteHom_zero (coh : BiShiftCoherence Syn)
    (Z : Syn) (w t m : ℤ) (hk : t-w=(0:ℕ)) (q : ℕ) (hq : 1 ≤ q)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree 0)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree 0)).IsTriangulated]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-w)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-w)).IsTriangulated]
    (z : (lambdaTower ((SyntheticCategory.biShift (0,-w)).obj Z)).FirstPage (0,m))
    (hz : z ∈ (lambdaTower ((SyntheticCategory.biShift (0,-w)).obj Z)).cycles q hq (0,m)) :
    ∃ a : HomotopyGroup (m-0)
        ((SyntheticCategory.biShift (0,-t)).obj (XModLambdaN Z q)),
      a ≫ (SyntheticCategory.biShift (0,-t)).map (XModLambdaN.restriction coh Z 1 q hq) =
        z ≫ (lambdaLayerIso ((SyntheticCategory.biShift (0,-w)).obj Z) 0).hom ≫
          (lambdaFirstLayerNormalizedIso coh Z w t 0 hk).hom := by
  have hw : w=t := by omega
  subst w
  exact raw_cycles_finiteHom coh Z t m q hq z hz

omit [HasFunctorialCofiber (C := Syn)] in
private theorem degreeCast_comp {A B : Syn} {m n : ℤ} (h : m=n)
    (a : HomotopyGroup m A) (f : A ⟶ B) :
    degreeCast h (a ≫ f) = degreeCast h a ≫ f := by
  subst n
  rfl

private def weightHomCoordinate (Z : Syn) (m t : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-t)).Additive] :
    HomotopyGroup m ((SyntheticCategory.biShift (0,-t)).obj Z) ≃+ BiHom m t Z :=
  (homotopyBiHomZeroEquiv _ m).trans (biHomWeightShiftEquiv Z m t).symm

omit [HasFunctorialCofiber (C := Syn)] in
private theorem biHomWeightShift_natural {A B : Syn} (m t : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-t)).Additive]
    (a : BiHom m t A) (f : A ⟶ B) :
    biHomWeightShiftEquiv B m t (a ≫ f) =
      biHomWeightShiftEquiv A m t a ≫ (SyntheticCategory.biShift (0,-t)).map f := by
  change (biShiftAddIso (m,t) (0,-t) (m,0) (by ext <;> simp)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,-t)).map (a ≫ f) ≫ 𝟙 _ =
    ((biShiftAddIso (m,t) (0,-t) (m,0) (by ext <;> simp)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,-t)).map a ≫ 𝟙 _) ≫ _
  simp only [Functor.map_comp, Category.comp_id, Category.assoc]

omit [HasFunctorialCofiber (C := Syn)] in
private theorem weightHomCoordinate_natural {A B : Syn} (m t : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-t)).Additive]
    (a : HomotopyGroup m ((SyntheticCategory.biShift (0,-t)).obj A)) (f : A ⟶ B) :
    weightHomCoordinate B m t (a ≫ (SyntheticCategory.biShift (0,-t)).map f) =
      weightHomCoordinate A m t a ≫ f := by
  apply (biHomWeightShiftEquiv B m t).injective
  rw [biHomWeightShift_natural]
  change (biHomWeightShiftEquiv B m t)
      ((biHomWeightShiftEquiv B m t).symm
        (homotopyBiHomZeroEquiv _ m (a ≫ (SyntheticCategory.biShift (0,-t)).map f))) =
    (biHomWeightShiftEquiv A m t)
      ((biHomWeightShiftEquiv A m t).symm (homotopyBiHomZeroEquiv _ m a)) ≫ _
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact (Category.assoc _ _ _).symm

private def initialRawIso (X : Syn) (p : ℤ × ℤ × ℤ) (k : ℕ)
    (hk : p.2.1-p.2.2 = (k : ℤ)) :
    (lambdaSequence X).Page 2 p ≅ ModuleCat.of ℤ
      ((lambdaTower ((SyntheticCategory.biShift (0,-p.2.2)).obj X)).FirstPage
        ((k : ℤ), p.2.1-p.1+k)) := by
  let Y := (SyntheticCategory.biShift (0,-p.2.2)).obj X
  have hgrade : lambdaGrading p = ((k : ℤ), p.2.1-p.1+k) := by
    ext <;> dsimp [lambdaGrading] <;> omega
  exact eqToIso (lambdaPage_eq X 2 p) ≪≫
    eqToIso (congrArg ((lambdaRawSequence Y).Page 1) hgrade) ≪≫
      rawFirstPageIso (lambdaTower Y) ((k : ℤ), p.2.1-p.1+k)

omit [HasFunctorialCofiber (C := Syn)] in
private theorem degreeCast_eqToIso {A : Syn} {m n : ℤ} (h : m=n)
    (a : HomotopyGroup m A) :
    (ConcreteCategory.hom (eqToIso (congrArg (fun j => ModuleCat.of ℤ (HomotopyGroup j A)) h)).hom) a =
      degreeCast h a := by
  subst n
  rfl

private theorem initialQuotient_value (coh : BiShiftCoherence Syn)
    (X : Syn) (p : ℤ × ℤ × ℤ) (k : ℕ)
    (hk : p.2.1-p.2.2 = (k : ℤ))
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).IsTriangulated]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-p.2.2)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-p.2.2)).IsTriangulated]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-p.2.1)).Additive]
    (z : (lambdaSequence X).Page 2 p) :
    (lambdaInitialQuotientIso coh X p k hk).hom z =
      weightHomCoordinate (XModLambdaN X 1) (p.2.1-p.1) p.2.1
        (degreeCast (show p.2.1-p.1+k-k=p.2.1-p.1 by omega)
          ((initialRawIso X p k hk).hom z ≫
            (lambdaLayerIso ((SyntheticCategory.biShift (0,-p.2.2)).obj X) k).hom) ≫
              (lambdaFirstLayerNormalizedIso coh X p.2.2 p.2.1 k hk).hom) := by
  change weightHomCoordinate (XModLambdaN X 1) (p.2.1-p.1) p.2.1
    ((eqToIso (congrArg (fun j => ModuleCat.of ℤ (HomotopyGroup j
        ((SyntheticCategory.biShift (lambdaDegree k)).obj
          (XModLambdaN ((SyntheticCategory.biShift (0,-p.2.2)).obj X) 1))))
        (show p.2.1-p.1+k-k=p.2.1-p.1 by omega))).hom
      ((initialRawIso X p k hk).hom z ≫
        (lambdaLayerIso ((SyntheticCategory.biShift (0,-p.2.2)).obj X) k).hom) ≫
        (lambdaFirstLayerNormalizedIso coh X p.2.2 p.2.1 k hk).hom) = _
  rw [degreeCast_eqToIso]


/-- Every continuation has an E₂-labelled outgoing differential value. -/
private theorem reachesPage_iff_exists_hasDifferential
    {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ × ℤ)
    (hdeg : p + E.diffDeg r = q) (x : E.Page 2 p) :
    ReachesPage E r p x ↔ ∃ y : E.Page 2 q, HasDifferential E r p q x y := by
  constructor
  · rintro ⟨xr, hxr⟩
    let D := E.ssData q
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r - E.r₀).toNat
    have hnm : n ≤ m := by
      dsimp only [n, m]
      exact_mod_cast (show (2 - E.r₀).toNat ≤ (r - E.r₀).toNat by omega)
    let yr : E.Page r q := (E.d r p ≫ eqToHom (congrArg (E.Page r) hdeg)) xr
    letI : Epi (D.pageπ m) := coequalizer.π_epi
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.pageπ m)).mp inferInstance yr
    let y : E.Page 2 q :=
      (Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hnm) ≫ D.pageπ n) z
    exact ⟨y, hdeg, xr, yr, hxr, ⟨hr, z, rfl, hz⟩, rfl⟩
  · rintro ⟨y, _, xr, yr, hxr, hyr, hd⟩
    exact ⟨xr, hxr⟩


private theorem initial_rep_transport
    {D D' : SSData (ModuleCat.{v} ℤ)} (h : D = D') (n : ℕ) (x : D.page 0)
    (hx : ∃ z : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti (show (0:WithTop ℕ) ≤ n from bot_le)) ≫
        D.pageπ 0) z = x) :
    ∃ z : (Subobject.underlying.obj (D'.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D'.Z n) (D'.Z 0) (D'.Z_anti (show (0:WithTop ℕ) ≤ n from bot_le)) ≫
        D'.pageπ 0) z = (eqToIso (congrArg (fun E => E.page 0) h)).hom x := by
  subst D'
  simpa only [eqToIso_refl, Iso.refl_hom, ModuleCat.id_apply] using hx

private theorem raw_initial_rep_cycles (T : RawTower Syn) (p : ℤ × ℤ)
    {D : SSData (ModuleCat.{v} ℤ)} (h : D = towerSSData T p) (n : ℕ) (x : D.page 0)
    (hx : ∃ z : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti (show (0:WithTop ℕ) ≤ n from bot_le)) ≫
        D.pageπ 0) z = x) :
    (rawFirstPageIso T p).hom ((eqToIso (congrArg (fun E => E.page 0) h)).hom x) ∈
      T.cycles (n+1) (by omega) p := by
  obtain ⟨z,hz⟩ := initial_rep_transport h n x hx
  rw [← hz, rawFirstPageIso_cycleRep]
  exact cycleRep_mem T p n z

private theorem lambdaData_eq_raw (Z : Syn) (p : ℤ × ℤ × ℤ) (k : ℕ)
    (hk : p.2.1-p.2.2=(k:ℤ)) :
    (lambdaSequence Z).ssData p =
      towerSSData (lambdaTower ((SyntheticCategory.biShift (0,-p.2.2)).obj Z))
        ((k:ℤ),p.2.1-p.1+k) := by
  change towerSSData _ (lambdaGrading p) = _
  congr 1
  ext <;> dsimp [lambdaGrading] <;> omega

private theorem initialRawIso_eq (Z : Syn) (p : ℤ × ℤ × ℤ) (k : ℕ)
    (hk : p.2.1-p.2.2=(k:ℤ)) :
    initialRawIso Z p k hk =
      eqToIso (congrArg (fun D => D.page 0) (lambdaData_eq_raw Z p k hk)) ≪≫
        rawFirstPageIso
          (lambdaTower ((SyntheticCategory.biShift (0,-p.2.2)).obj Z))
          ((k:ℤ),p.2.1-p.1+k) := by
  apply Iso.ext
  simp only [initialRawIso, Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc]


end
end KIP126.Literature.Paper38AllSpectrum
end

@[expose] section
namespace KIP126.Literature.Paper38AllSpectrum
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Synthetic.SpectralSequence
open KIP126.Literature.BocksteinRaw KIP126.Literature.Paper38ComparisonInput
open KIP126.Literature.Paper38BoundaryInput
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
attribute [local instance] fixedShiftAdditive fixedShiftCommShift fixedShiftTriangulated


private theorem lambda_representative_finiteLift (X : Spectrum) (q : ℕ)
    (hq : 1 ≤ q) (s t : ℤ)
    (x : (lambdaSS X).Page 2 (s,t,t-(0:ℕ)))
    (xr : (lambdaSS X).Page (q+1) (s,t,t-(0:ℕ)))
    (hx : SyntheticRepresentsOnPage (lambdaSS X) (q+1) (s,t,t-(0:ℕ)) x xr) :
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q),
      a ≫ (background.quotients.tower (nuZeroSpectrum X)).rho 1 q hq =
        (baseInitialQuotientIso X s t 0).hom x := by
  let Z := nuZeroSpectrum X
  let p : ℤ × ℤ × ℤ := (s,t,t-(0:ℕ))
  let T := lambdaTower ((SyntheticCategory.biShift (0,-p.2.2)).obj Z)
  have hk : p.2.1-p.2.2=(0:ℕ) := by dsimp [p]; omega
  let n := ((q:ℤ)+1-2).toNat
  have hn : n+1=q := by dsimp [n]; omega
  obtain ⟨_, z, hz, _⟩ := hx
  have hc := raw_initial_rep_cycles T ((0:ℕ),p.2.1-p.1+(0:ℕ))
    (lambdaData_eq_raw Z p 0 hk) n x ⟨z,hz⟩
  have hc' : (initialRawIso Z p 0 hk).hom x ∈
      T.cycles q hq ((0:ℕ),p.2.1-p.1+(0:ℕ)) := by
    rw [initialRawIso_eq]
    change (rawFirstPageIso T _).hom
      ((eqToIso (congrArg (fun D => D.page 0) (lambdaData_eq_raw Z p 0 hk))).hom x) ∈ _
    simpa only [hn] using hc
  obtain ⟨a,ha⟩ := raw_cycles_finiteHom_zero background.quotients.coherence Z
    p.2.2 p.2.1 (p.2.1-p.1+(0:ℕ)) hk q hq
      ((initialRawIso Z p 0 hk).hom x) hc'
  have hm : p.2.1-p.1+(0:ℕ)-0=p.2.1-p.1 := by omega
  let a' := degreeCast hm a
  refine ⟨weightHomCoordinate (XModLambdaN Z q) (t-s) t a', ?_⟩
  rw [background.quotients.restriction]
  rw [← weightHomCoordinate_natural]
  have ha' := congrArg (degreeCast hm) ha
  rw [degreeCast_comp (a := a)] at ha'
  rw [← Category.assoc, degreeCast_comp] at ha'
  change weightHomCoordinate (XModLambdaN Z 1) (p.2.1-p.1) p.2.1
      (a' ≫ (SyntheticCategory.biShift (0,-p.2.1)).map
        (XModLambdaN.restriction background.quotients.coherence Z 1 q hq)) = _
  rw [ha']
  change _ = (lambdaInitialQuotientIso background.quotients.coherence Z p 0 hk).hom x
  exact (initialQuotient_value background.quotients.coherence Z p 0 hk x).symm


/-- Classical E₂ labels reaching page q+1 admit a finite lift, for every
spectrum in the specified category. -/
private theorem classical_reaches_finiteLift (X : Spectrum) (q : ℕ)
    (hq : 0 < q) (s t : ℤ)
    (x : (background.classical.obj X).Page 2 (s,t))
    (hx : ReachesPage (background.classical.obj X) (q+1) (s,t) x) :
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q),
      a ≫ (background.quotients.tower (nuZeroSpectrum X)).rho 1 q hq =
        comparisonData.classicalFirst X s t x := by
  have hdeg : (s,t) + (background.classical.obj X).diffDeg (q+1) =
      (s+(q+1:ℕ),t+(q+1:ℕ)-1) := by
    rw [background.classical.differentialDegree]
    ext <;> dsimp
    omega
  obtain ⟨y,hy⟩ := (reachesPage_iff_exists_hasDifferential
    (background.classical.obj X) (q+1) (by omega) (s,t)
    (s+(q+1:ℕ),t+(q+1:ℕ)-1) hdeg x).mp hx
  have h := (comparisonData.classical_differential X s t (q+1) 0
    (by omega) x y).mp hy
  obtain ⟨_,xr,_,hxr,_,_⟩ := h
  obtain ⟨a,ha⟩ := lambda_representative_finiteLift X q hq s t
    ((baseInitialQuotientIso X s t 0).inv
      (comparisonData.classicalFirst X s t x)) xr hxr
  refine ⟨a, ?_⟩
  simpa only [Iso.inv_hom_id_apply] using ha


private theorem allSpectrum_classical_finite_differential (X : Spectrum)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : (background.classical.obj X).Page 2 (s,t))
    (y : (background.classical.obj X).Page 2 (s+q+1,t+q)) :
    HasDifferential (background.classical.obj X) (q+1)
      (s,t) (s+q+1,t+q) x y ↔
    SyntheticHasDifferential (lambdaSS X) (q+1)
      (s,t,t-(0 : ℕ)) (s+q+1,t+q,(t+q)-q)
      ((baseInitialQuotientIso X s t 0).inv
        (comparisonData.classicalFirst X s t x))
      ((baseInitialQuotientIso X (s+q+1) (t+q) q).inv
        (comparisonData.classicalFirst X (s+q+1) (t+q) y)) := by
  have h := comparisonData.classical_differential X s t (q+1) 0 (by omega) x
  have hs : s + ((q+1 : ℕ) : ℤ) = s+q+1 := by omega
  have ht : t + ((q+1 : ℕ) : ℤ) - 1 = t+q := by omega
  have hk : (0 : ℕ)+(q+1-1) = q := by omega
  rw [hs, ht, hk] at h
  exact h y

/-- The actual differential value of any given finite quotient lift,
expressed by the original classical comparison labels. -/
private theorem allSpectrum_lift_differential (X : Spectrum)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q)) :
    HasDifferential (background.classical.obj X) (q+1)
      (s,t) (s+q+1,t+q)
      ((comparisonData.classicalFirst X s t).symm
        (a ≫ (background.quotients.tower (nuZeroSpectrum X)).rho 1 q hq))
      ((comparisonData.classicalFirst X (s+q+1) (t+q)).symm
        (geometricBoundaryLabel X q hq s t a)) := by
  apply (allSpectrum_classical_finite_differential X q hq s t _ _).mpr
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact lambda_geometric_boundary_input X q hq s t a

/-- The finite-lift criterion for every spectrum. -/
private theorem allSpectrum_finite_lift (X : Spectrum) (q : ℕ)
    (hq : 0 < q) (s t : ℤ)
    (x : (background.classical.obj X).Page 2 (s,t)) :
    ReachesPage (background.classical.obj X) (q+1) (s,t) x ↔
      ∃ a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q),
        a ≫ (background.quotients.tower (nuZeroSpectrum X)).rho 1 q hq =
          comparisonData.classicalFirst X s t x := by
  constructor
  · exact classical_reaches_finiteLift X q hq s t x
  · rintro ⟨a,ha⟩
    have h := allSpectrum_lift_differential X q hq s t a
    rw [ha, LinearEquiv.symm_apply_apply] at h
    obtain ⟨_,xr,_,hxr,_,_⟩ := h
    exact ⟨xr,hxr⟩

/-- A continuation has one finite lift whose actual quotient boundary
represents its classical outgoing differential. -/
private theorem allSpectrum_finite_boundary (X : Spectrum) (q : ℕ)
    (hq : 0 < q) (s t : ℤ)
    (x : (background.classical.obj X).Page 2 (s,t))
    (hx : ReachesPage (background.classical.obj X) (q+1) (s,t) x) :
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q),
      a ≫ (background.quotients.tower (nuZeroSpectrum X)).rho 1 q hq =
        comparisonData.classicalFirst X s t x ∧
      HasDifferential (background.classical.obj X) (q+1)
        (s,t) (s+q+1,t+q) x
        ((comparisonData.classicalFirst X (s+q+1) (t+q)).symm
          (geometricBoundaryLabel X q hq s t a)) := by
  obtain ⟨a,ha⟩ := (allSpectrum_finite_lift X q hq s t x).mp hx
  refine ⟨a,ha,?_⟩
  have h := allSpectrum_lift_differential X q hq s t a
  rwa [ha, LinearEquiv.symm_apply_apply] at h

/-- The geometric boundary of a finite lift and its specified classical
differential target agree on the later page, including earlier boundaries. -/
private theorem allSpectrum_specified_differential (X : Spectrum) (q : ℕ)
    (hq : 0 < q) (s t : ℤ)
    (x : (background.classical.obj X).Page 2 (s,t))
    (y : (background.classical.obj X).Page 2 (s+q+1,t+q))
    (hxy : HasDifferential (background.classical.obj X) (q+1)
      (s,t) (s+q+1,t+q) x y) :
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) q),
      a ≫ (background.quotients.tower (nuZeroSpectrum X)).rho 1 q hq =
        comparisonData.classicalFirst X s t x ∧
      ∃ yr : (background.classical.obj X).Page (q+1) (s+q+1,t+q),
        RepresentsOnPage (background.classical.obj X) (q+1) (s+q+1,t+q) y yr ∧
        RepresentsOnPage (background.classical.obj X) (q+1) (s+q+1,t+q)
          ((comparisonData.classicalFirst X (s+q+1) (t+q)).symm
            (geometricBoundaryLabel X q hq s t a)) yr := by
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := hxy
  obtain ⟨a,ha,hβ⟩ := allSpectrum_finite_boundary X q hq s t x ⟨xr,hxr⟩
  obtain ⟨hdeg',xr',yr',hxr',hyr',hd'⟩ := hβ
  have he : xr=xr' := RepresentsOnPage.unique hxr hxr'
  subst xr'
  have he' : yr=yr' := hd.symm.trans hd'
  exact ⟨a,ha,yr,hyr,he'.symm ▸ hyr'⟩


end
end KIP126.Literature.Paper38AllSpectrum
end
