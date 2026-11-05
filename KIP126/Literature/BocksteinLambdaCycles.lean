module
import all KIP126.Literature.BocksteinLambdaTower

/-!
# Cycles and boundary truncation for the actual lambda tower

The cycle criterion uses the fixed `lambdaLayerIso` from
`BocksteinLambdaTower` and the actual finite-quotient restriction maps.
The boundary bounds use the same nonnegative tower and its spectral-sequence
data. All constructions and lemmas remain internal to Literature.
-/

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C:=C)]
private def cofiberCompositeMap {A B D : C} (g : A ⟶ B) (f : B ⟶ D) :
    HasFunctorialCofiber.cofib (g ≫ f) ⟶ HasFunctorialCofiber.cofib f :=
  HasFunctorialCofiber.cofibMap (g ≫ f) f g (𝟙 _) (by simp)

/-- Exact-couple cycles are images from the finite composite cofiber
for the specified square completion. -/
private theorem cofiberCompositeMap_range {A B D P : C} (g : A ⟶ B) (f : B ⟶ D)
    (x : P ⟶ HasFunctorialCofiber.cofib f) :
    (∃ z, z ≫ cofiberCompositeMap g f = x) ↔
      ∃ a : P ⟶ A⟦(1 : ℤ)⟧,
        x ≫ HasFunctorialCofiber.cofibδ f = a ≫ (shiftFunctor C (1 : ℤ)).map g := by
  let h := cofiberCompositeMap g f
  have hδ : h ≫ HasFunctorialCofiber.cofibδ f =
      HasFunctorialCofiber.cofibδ (g ≫ f) ≫ (shiftFunctor C (1 : ℤ)).map g :=
    HasFunctorialCofiber.cofibMap_δ _ _ _ _ _
  have hι : HasFunctorialCofiber.cofibι (g ≫ f) ≫ h =
      HasFunctorialCofiber.cofibι f := by
    simpa only [h, cofiberCompositeMap, Category.id_comp] using
      (HasFunctorialCofiber.cofibMap_ι (g ≫ f) f g (𝟙 _) (by simp)).symm
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z ≫ HasFunctorialCofiber.cofibδ (g ≫ f), by rw [Category.assoc, hδ, Category.assoc]⟩
  · rintro ⟨a,ha⟩
    have hzero : HasFunctorialCofiber.cofibδ f ≫ (shiftFunctor C (1 : ℤ)).map f = 0 :=
      comp_distTriang_mor_zero₃₁ _ (HasFunctorialCofiber.cofib_distinguished f)
    have ha0 : a ≫ (shiftFunctor C (1 : ℤ)).map (g ≫ f) = 0 := by
      rw [Functor.map_comp, ← Category.assoc, ← ha, Category.assoc, hzero, comp_zero]
    obtain ⟨z,hz⟩ : ∃ z : P ⟶ HasFunctorialCofiber.cofib (g ≫ f),
        a = z ≫ HasFunctorialCofiber.cofibδ (g ≫ f) := Triangle.coyoneda_exact₁ _
      (HasFunctorialCofiber.cofib_distinguished (g ≫ f)) a ha0
    have hdiff : (x-z ≫ h) ≫ HasFunctorialCofiber.cofibδ f = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hδ, ← Category.assoc, ← hz, ha, sub_self]
    obtain ⟨y,hy⟩ : ∃ y : P ⟶ D,
        x-z ≫ h = y ≫ HasFunctorialCofiber.cofibι f := Triangle.coyoneda_exact₃ _
      (HasFunctorialCofiber.cofib_distinguished f) (x-z ≫ h) hdiff
    refine ⟨z+y ≫ HasFunctorialCofiber.cofibι (g ≫ f), ?_⟩
    change (z+y ≫ HasFunctorialCofiber.cofibι (g ≫ f)) ≫ h = x
    rw [Preadditive.add_comp, Category.assoc, hι, ← hy]
    abel

omit [HasFunctorialCofiber (C := C)] in
private theorem raw_desuspend_natural {A B : C} (g : A ⟶ B) (n : ℤ)
    (x : HomotopyGroup n (A⟦(1 : ℤ)⟧)) :
    RawTower.desuspend B n (x ≫ (shiftFunctor C (1 : ℤ)).map g) =
      RawTower.desuspend A n x ≫ g := by
  let F := shiftFunctor C (-1 : ℤ)
  let a := (shiftFunctorAdd' C n (-1) (n-1) (by omega)).app SphereSpectrum
  let b := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
  change a.hom ≫ F.map (x ≫ (shiftFunctor C (1 : ℤ)).map g) ≫ (b.app B).hom =
    (a.hom ≫ F.map x ≫ (b.app A).hom) ≫ g
  rw [Functor.map_comp]
  have hb : (b.app A).hom ≫ g =
      F.map ((shiftFunctor C (1 : ℤ)).map g) ≫ (b.app B).hom :=
    (b.hom.naturality g).symm
  simp only [Category.assoc, hb]

omit [HasFunctorialCofiber (C := C)] in
private theorem raw_desuspend_bijective (A : C) (n : ℤ) :
    Function.Bijective (RawTower.desuspend A n) := by
  let F := shiftFunctor C (-1 : ℤ)
  let a := (shiftFunctorAdd' C n (-1) (n-1) (by omega)).app SphereSpectrum
  let b := (shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).app A
  constructor
  · intro x y h
    apply F.map_injective
    change a.hom ≫ F.map x ≫ b.hom = a.hom ≫ F.map y ≫ b.hom at h
    simpa only [cancel_epi, cancel_mono] using h
  · intro y
    let x := F.preimage (a.inv ≫ y ≫ b.inv)
    refine ⟨x, ?_⟩
    change a.hom ≫ F.map x ≫ b.hom = y
    rw [show F.map x = a.inv ≫ y ≫ b.inv from F.map_preimage _]
    simp

omit [HasFunctorialCofiber (C := C)] in
private theorem raw_desuspend_range_iff {A B : C} (g : A ⟶ B) (n : ℤ)
    (x : HomotopyGroup n (B⟦(1 : ℤ)⟧)) :
    (∃ y : HomotopyGroup (n-1) A, y ≫ g = RawTower.desuspend B n x) ↔
      ∃ a : HomotopyGroup n (A⟦(1 : ℤ)⟧),
        x = a ≫ (shiftFunctor C (1 : ℤ)).map g := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨a,ha⟩ := (raw_desuspend_bijective A n).surjective y
    refine ⟨a, (raw_desuspend_bijective B n).injective ?_⟩
    rw [raw_desuspend_natural, ha, hy]
  · rintro ⟨a,rfl⟩
    exact ⟨RawTower.desuspend A n a, (raw_desuspend_natural g n a).symm⟩


/-- A raw-tower r-cycle lifts from its finite composite cofiber along
the square-completion map. -/
private theorem raw_cycles_iff_finite_composite_lift (T : RawTower C)
    (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) (x : T.FirstPage p) :
    x ∈ T.cycles r hr p ↔
      ∃ z : HomotopyGroup (p.2-p.1)
        (HasFunctorialCofiber.cofib
          (T.mapAt (show p.1+1 ≤ p.1+r by omega) ≫
            T.mapAt (show p.1 ≤ p.1+1 by omega))),
        z ≫ cofiberCompositeMap
          (T.mapAt (show p.1+1 ≤ p.1+r by omega))
          (T.mapAt (show p.1 ≤ p.1+1 by omega)) = x := by
  let g := T.mapAt (show p.1+1 ≤ p.1+r by omega)
  let f := T.mapAt (show p.1 ≤ p.1+1 by omega)
  change (∃ y : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)),
      y ≫ g = RawTower.desuspend _ _ (x ≫ HasFunctorialCofiber.cofibδ f)) ↔
    ∃ z, z ≫ cofiberCompositeMap g f = x
  rw [raw_desuspend_range_iff, cofiberCompositeMap_range]


end
end KIP126.Literature.BocksteinRaw
end

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private theorem lambdaShift_associativity' (coh : BiShiftCoherence Syn)
    (i j k ij jk total : ℕ) (hij : i + j = ij) (hjk : j + k = jk)
    (htotal : ij + k = total) (htotal' : i + jk = total) (X : Syn) :
    (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).map
          ((lambdaShiftAddIso i j ij hij).hom.app X) ≫
        (lambdaShiftAddIso ij k total htotal).hom.app X =
      (lambdaShiftAddIso j k jk hjk).hom.app
          ((SyntheticCategory.biShift (Syn := Syn) (lambdaDegree i)).obj X) ≫
        (lambdaShiftAddIso i jk total htotal').hom.app X := by
  exact coh.associativity (lambdaDegree i) (lambdaDegree j) (lambdaDegree k)
    (lambdaDegree ij) (lambdaDegree jk) (lambdaDegree total) _ _ _ _ X

private theorem lambdaRestrictionPieces_comp (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (htotal : ab + c = total) (htotal' : a + bc = total) (X : Syn) :
    ((lambdaShiftAddIso a bc total htotal').inv.app X ≫
      (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree bc)).map (lambdaPow a X)) ≫
    ((lambdaShiftAddIso b c bc hbc).inv.app X ≫
      (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map (lambdaPow b X)) =
    (lambdaShiftAddIso ab c total htotal).inv.app X ≫
      (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map (lambdaPow ab X) := by
  apply (cancel_epi
    ((SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map
      ((lambdaShiftAddIso a b ab hab).hom.app X) ≫
      (lambdaShiftAddIso ab c total htotal).hom.app X)).mp
  calc
    _ = (lambdaShiftAddIso b c bc hbc).hom.app
          ((SyntheticCategory.biShift (Syn := Syn) (lambdaDegree a)).obj X) ≫
        (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree bc)).map (lambdaPow a X) ≫
        (lambdaShiftAddIso b c bc hbc).inv.app X ≫
        (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map (lambdaPow b X) := by
      rw [lambdaShift_associativity' coh a b c ab bc total hab hbc htotal htotal']
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map
        ((SyntheticCategory.biShift (Syn := Syn) (lambdaDegree b)).map (lambdaPow a X)) ≫
        (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map (lambdaPow b X) := by
      rw [← NatTrans.naturality_assoc]
      simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]
    _ = (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map
        ((lambdaShiftAddIso a b ab hab).hom.app X ≫ lambdaPow ab X) := by
      rw [lambdaPow_add_comparison coh a b ab hab X, Functor.map_comp]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem lambdaRestrictionSourceMap_comp (coh : BiShiftCoherence Syn)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (X : Syn) :
    lambdaRestrictionSourceMap j k hjk X ≫ lambdaRestrictionSourceMap i j hij X =
      lambdaRestrictionSourceMap i k (hij.trans hjk) X := by
  exact lambdaRestrictionPieces_comp coh (k-j) (j-i) i (k-i) j k
    (by omega) (Nat.sub_add_cancel hij) (Nat.sub_add_cancel (hij.trans hjk))
    (Nat.sub_add_cancel hjk) X

private theorem lambdaTower_map [HasFunctorialCofiber (C := Syn)]
    (coh : BiShiftCoherence Syn) (X : Syn) {i j : ℕ} (hij : i ≤ j) :
    (lambdaTower X).map hij = lambdaRestrictionSourceMap i j hij X := by
  induction j, hij using Nat.le_induction with
  | base =>
    rw [RawTower.map_self, lambdaRestrictionSourceMap_self coh]
    rfl
  | succ j hij ih =>
    rw [← (lambdaTower X).map_comp hij (Nat.le_succ j), lambdaTower_succ, ih]
    exact lambdaRestrictionSourceMap_comp coh i j (j+1) hij (Nat.le_succ j) X

end
end KIP126.Literature.BocksteinRaw

end


@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private theorem lambdaRestrictionPieces_shift (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (htotal : ab + c = total) (htotal' : a + bc = total) (X : Syn) :
    ((lambdaShiftAddIso a bc total htotal').inv.app X ≫
      (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree bc)).map (lambdaPow a X)) ≫
        (lambdaShiftAddIso b c bc hbc).inv.app X =
    (lambdaShiftAddIso ab c total htotal).inv.app X ≫
      (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map
        ((lambdaShiftAddIso a b ab hab).inv.app X ≫
          (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree b)).map (lambdaPow a X)) := by
  apply (cancel_epi
    ((SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map
      ((lambdaShiftAddIso a b ab hab).hom.app X) ≫
      (lambdaShiftAddIso ab c total htotal).hom.app X)).mp
  calc
    _ = (lambdaShiftAddIso b c bc hbc).hom.app
          ((SyntheticCategory.biShift (Syn := Syn) (lambdaDegree a)).obj X) ≫
        (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree bc)).map (lambdaPow a X) ≫
          (lambdaShiftAddIso b c bc hbc).inv.app X := by
      rw [lambdaShift_associativity' coh a b c ab bc total hab hbc htotal htotal']
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree c)).map
        ((SyntheticCategory.biShift (Syn := Syn) (lambdaDegree b)).map (lambdaPow a X)) := by
      rw [← NatTrans.naturality_assoc]
      simp only [Functor.comp_map, Iso.hom_inv_id_app, Category.comp_id]
    _ = _ := by
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp]
      simp only [Iso.hom_inv_id_app_assoc]

/-- Compatibility of the lambda-restriction source square with the
specified lambda-axis shift comparisons. -/
private theorem lambdaRestrictionSourceMap_shift_square (coh : BiShiftCoherence Syn)
    (X : Syn) (k r : ℕ) (hr : 1 ≤ r) :
    lambdaRestrictionSourceMap (k+1) (k+r) (by omega) X ≫
        (lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X =
      (lambdaShiftAddIso r k (k+r) (by omega)).inv.app X ≫
        (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).map
          (lambdaRestrictionSourceMap 1 r hr X) := by
  have hsub : k+r-(k+1) = r-1 := by omega
  unfold lambdaRestrictionSourceMap
  have hgen (a : ℕ) (ha : a = r-1) :
      ((lambdaShiftAddIso a (k+1) (k+r) (by omega)).inv.app X ≫
        (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree (k+1))).map
          (lambdaPow a X)) ≫
        (lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X =
      (lambdaShiftAddIso r k (k+r) (by omega)).inv.app X ≫
        (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree k)).map
          ((lambdaShiftAddIso (r-1) 1 r (by omega)).inv.app X ≫
            (SyntheticCategory.biShift (Syn := Syn) (lambdaDegree 1)).map
              (lambdaPow (r-1) X)) := by
    subst a
    exact lambdaRestrictionPieces_shift coh (r-1) 1 k r (k+1) (k+r)
      (by omega) (by omega) (by omega) (by omega) X
  exact hgen (k+r-(k+1)) hsub

end
end KIP126.Literature.BocksteinRaw
end


@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private theorem lambdaRestriction_shift_range (coh : BiShiftCoherence Syn)
    (X : Syn) (i j : ℕ) (hij : i ≤ j) (F : Syn ⥤ Syn)
    [F.CommShift ℤ] [F.IsTriangulated] {P : Syn}
    (x : P ⟶ F.obj (XModLambdaN X i)) :
    (∃ z : P ⟶ F.obj (XModLambdaN X j),
      z ≫ F.map (XModLambdaN.restriction coh X i j hij) = x) ↔
      ∃ a : P ⟶ (F.obj ((SyntheticCategory.biShift (lambdaDegree j)).obj X))⟦(1:ℤ)⟧,
        x ≫ F.map (XModLambdaN.proj X i) ≫
          (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree i)).obj X) =
        a ≫ (shiftFunctor Syn (1:ℤ)).map (F.map (lambdaRestrictionSourceMap i j hij X)) := by
  let h := F.map (XModLambdaN.restriction coh X i j hij)
  let g := F.map (lambdaRestrictionSourceMap i j hij X)
  let Ti := F.mapTriangle.obj (XModLambdaN.cofiberTriangle X i)
  let Tj := F.mapTriangle.obj (XModLambdaN.cofiberTriangle X j)
  have hi := F.map_distinguished _ (XModLambdaN.cofiberTriangle_distinguished X i)
  have hj := F.map_distinguished _ (XModLambdaN.cofiberTriangle_distinguished X j)
  have hδ : h ≫ Ti.mor₃ = Tj.mor₃ ≫ (shiftFunctor Syn (1:ℤ)).map g := by
    have he : XModLambdaN.restriction coh X i j hij ≫ XModLambdaN.proj X i =
      XModLambdaN.proj X j ≫ (shiftFunctor Syn (1:ℤ)).map (lambdaRestrictionSourceMap i j hij X) :=
        HasFunctorialCofiber.cofibMap_δ _ _ _ _ _
    change F.map (XModLambdaN.restriction coh X i j hij) ≫ F.map (XModLambdaN.proj X i) ≫
      (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree i)).obj X) =
      (F.map (XModLambdaN.proj X j) ≫
        (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree j)).obj X)) ≫
      (shiftFunctor Syn (1:ℤ)).map (F.map (lambdaRestrictionSourceMap i j hij X))
    rw [← F.map_comp_assoc, he, F.map_comp]
    simp only [Category.assoc, F.commShiftIso_hom_naturality]
    rfl
  have hι : Tj.mor₂ ≫ h = Ti.mor₂ := by
    change F.map (XModLambdaN.incl X j) ≫ F.map (XModLambdaN.restriction coh X i j hij) =
      F.map (XModLambdaN.incl X i)
    rw [← F.map_comp, XModLambdaN.restriction_incl]
  have h₁ : g ≫ Ti.mor₁ = Tj.mor₁ := by
    change F.map (lambdaRestrictionSourceMap i j hij X) ≫ F.map (lambdaPow i X) =
      F.map (lambdaPow j X)
    rw [← F.map_comp, lambdaRestrictionSourceMap_commutes coh]
  change (∃ z, z ≫ h = x) ↔ ∃ a, x ≫ Ti.mor₃ = a ≫ (shiftFunctor Syn (1:ℤ)).map g
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z ≫ Tj.mor₃, by rw [Category.assoc, hδ, Category.assoc]⟩
  · rintro ⟨a,ha⟩
    have hzero : Ti.mor₃ ≫ (shiftFunctor Syn (1:ℤ)).map Ti.mor₁ = 0 :=
      comp_distTriang_mor_zero₃₁ _ hi
    have ha0 : a ≫ (shiftFunctor Syn (1:ℤ)).map Tj.mor₁ = 0 := by
      rw [← h₁, Functor.map_comp, ← Category.assoc, ← ha, Category.assoc, hzero, comp_zero]
    obtain ⟨z,hz⟩ : ∃ z : P ⟶ Tj.obj₃, a = z ≫ Tj.mor₃ :=
      Triangle.coyoneda_exact₁ _ hj a ha0
    have hdiff : (x-z ≫ h) ≫ Ti.mor₃ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hδ, ← Category.assoc, ← hz, ha, sub_self]
    obtain ⟨y,hy⟩ : ∃ y : P ⟶ Ti.obj₂, x-z ≫ h = y ≫ Ti.mor₂ :=
      Triangle.coyoneda_exact₃ _ hi (x-z ≫ h) hdiff
    refine ⟨z+y ≫ Tj.mor₂, ?_⟩
    rw [Preadditive.add_comp, Category.assoc, hι, ← hy]
    abel

omit [HasFunctorialCofiber (C:=Syn)] in
private theorem map_range_iff_iso {A B A' B' P : Syn}
    (eA : A ≅ A') (eB : B ≅ B') (g : A ⟶ B) (g' : A' ⟶ B')
    (he : g ≫ eB.hom = eA.hom ≫ g') (x : P ⟶ B) :
    (∃ a : P ⟶ A, x = a ≫ g) ↔
      ∃ a' : P ⟶ A', x ≫ eB.hom = a' ≫ g' := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a ≫ eA.hom, by rw [Category.assoc, he, Category.assoc]⟩
  · rintro ⟨a,ha⟩
    refine ⟨a ≫ eA.inv, ?_⟩
    apply (cancel_mono eB.hom).mp
    rw [Category.assoc, Category.assoc, he]
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.comp_id] using ha

private theorem raw_nat_cycles_iff {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C:=C)] (T : RawTower C)
    (k r : ℕ) (hr : 1 ≤ r) (n : ℤ) (x : T.FirstPage ((k:ℤ),n)) :
    x ∈ T.cycles r hr ((k:ℤ),n) ↔
      ∃ a : HomotopyGroup (n-k) ((T.stage (k+r))⟦(1:ℤ)⟧),
        x ≫ HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ k)) =
          a ≫ (shiftFunctor C (1:ℤ)).map (T.map (show k+1 ≤ k+r by omega)) := by
  let P (q : ℕ) (hq : k+1 ≤ q) : Prop :=
    ∃ y : HomotopyGroup (n-k-1) (T.stage q),
      y ≫ T.map hq = RawTower.desuspend _ _
        (x ≫ HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ k)))
  have hnorm (q : ℕ) (hq : k+1 ≤ q) (hqr : q=k+r) :
      P q hq ↔ P (k+r) (by omega) := by
    subst q
    rfl
  have hc : x ∈ T.cycles r hr ((k:ℤ),n) ↔ P (k+r) (by omega) :=
    hnorm (((k:ℤ)+(r:ℤ)).toNat) (by omega) (by omega)
  exact hc.trans (raw_desuspend_range_iff (T.map (show k+1 ≤ k+r by omega)) (n-k) _)


private theorem cofiber_delta_congr {A B : Syn} {f g : A ⟶ B} (h : f=g) :
    HasFunctorialCofiber.cofibδ f =
      (eqToIso (congrArg HasFunctorialCofiber.cofib h)).hom ≫ HasFunctorialCofiber.cofibδ g := by
  subst g
  simp

private theorem lambdaLayerIso_boundary (X : Syn) (k : ℕ)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).IsTriangulated] :
    HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k)) ≫
      (shiftFunctor Syn (1:ℤ)).map ((lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X) =
    (lambdaLayerIso X k).hom ≫
      (SyntheticCategory.biShift (lambdaDegree k)).map (XModLambdaN.proj X 1) ≫
      ((SyntheticCategory.biShift (lambdaDegree k)).commShiftIso (1:ℤ)).hom.app
        ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) := by
  have hd := cofiber_delta_congr (lambdaTower_succ X k)
  change HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k)) =
    (eqToIso (lambdaLayer_nat X k)).hom ≫ HasFunctorialCofiber.cofibδ (lambdaTowerStep X k) at hd
  rw [hd, Category.assoc, lambdaStepLayerIso_boundary]
  simp only [lambdaLayerIso, Iso.trans_hom, Category.assoc]

private theorem lambda_cycles_iff_shifted_restriction (coh : BiShiftCoherence Syn)
    (X : Syn) (k r : ℕ) (hr : 1 ≤ r) (n : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).IsTriangulated]
    (x : (lambdaTower X).FirstPage ((k:ℤ),n)) :
    x ∈ (lambdaTower X).cycles r hr ((k:ℤ),n) ↔
      ∃ z : HomotopyGroup (n-k)
        ((SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN X r)),
        z ≫ (SyntheticCategory.biShift (lambdaDegree k)).map
          (XModLambdaN.restriction coh X 1 r hr) = x ≫ (lambdaLayerIso X k).hom := by
  let F := SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)
  let eA := (shiftFunctor Syn (1:ℤ)).mapIso
    ((lambdaShiftAddIso r k (k+r) (by omega)).symm.app X)
  let eB := (shiftFunctor Syn (1:ℤ)).mapIso
    ((lambdaShiftAddIso 1 k (k+1) (by omega)).symm.app X)
  let g := (shiftFunctor Syn (1:ℤ)).map
    ((lambdaTower X).map (show k+1 ≤ k+r by omega))
  let g' := (shiftFunctor Syn (1:ℤ)).map
    (F.map (lambdaRestrictionSourceMap 1 r hr X))
  have he : g ≫ eB.hom = eA.hom ≫ g' := by
    change (shiftFunctor Syn (1:ℤ)).map _ ≫ (shiftFunctor Syn (1:ℤ)).map _ =
      (shiftFunctor Syn (1:ℤ)).map _ ≫ (shiftFunctor Syn (1:ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp, lambdaTower_map coh X]
    exact (shiftFunctor Syn (1:ℤ)).congr_map
      (lambdaRestrictionSourceMap_shift_square coh X k r hr)
  let b := x ≫ HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k))
  have hb : b ≫ eB.hom =
      (x ≫ (lambdaLayerIso X k).hom) ≫ F.map (XModLambdaN.proj X 1) ≫
        (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) := by
    change (x ≫ HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k))) ≫
      (shiftFunctor Syn (1:ℤ)).map ((lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X) = _
    rw [Category.assoc, lambdaLayerIso_boundary]
    exact (Category.assoc _ _ _).symm
  refine (raw_nat_cycles_iff (lambdaTower X) k r hr n x).trans ?_
  refine (map_range_iff_iso eA eB g g' he b).trans ?_
  have hm := congrArg (fun q => ∃ a, q = a ≫ g') hb
  refine (Iff.of_eq hm).trans ?_
  exact (lambdaRestriction_shift_range coh X 1 r hr F
    (x ≫ (lambdaLayerIso X k).hom)).symm

end
end KIP126.Literature.BocksteinRaw
end

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]

private theorem rawBoundaries_stabilize (T : RawTower C) (p : ℤ × ℤ)
    (k : ℕ) (hk : p.1 = k) (r : ℕ) (hr : k+1 ≤ r) :
    T.boundaries r (by omega) p = T.boundaries (k+1) (by omega) p := by
  have h1 : (p.1-(r:ℤ)+1).toNat = 0 := by omega
  have h2 : (p.1-((k+1:ℕ):ℤ)+1).toNat = 0 := by omega
  let F : {j : ℕ // j ≤ p.1.toNat} → Submodule ℤ
      (HomotopyGroup (p.2-p.1) (T.stageAt p.1)) := fun j =>
    (inducedMap (T.map j.property) (p.2-p.1)).toIntLinearMap.ker
  change (F ⟨(p.1-(r:ℤ)+1).toNat, by omega⟩).map (T.layerMap p) =
    (F ⟨(p.1-((k+1:ℕ):ℤ)+1).toNat, by omega⟩).map (T.layerMap p)
  exact congrArg (fun j => (F j).map (T.layerMap p))
    (Subtype.ext (h1.trans h2.symm))

private theorem rawBoundaries_truncate (T : RawTower C) (p : ℤ × ℤ)
    (k : ℕ) (hk : p.1 = k) (r : ℕ) (hr : 1 ≤ r) :
    T.boundaries r hr p = T.boundaries (min r (k+1)) (by omega) p := by
  by_cases h : r ≤ k+1
  · simp only [Nat.min_eq_left h]
  · simpa only [Nat.min_eq_right (show k+1 ≤ r by omega)] using
      rawBoundaries_stabilize T p k hk r (by omega)

private theorem rawFiniteBoundaries_truncate (T : RawTower C) (p : ℤ × ℤ)
    (k : ℕ) (hk : p.1 = k) (n : ℕ) :
    finiteBoundaries T p n = finiteBoundaries T p (min n k) := by
  unfold finiteBoundaries
  rw [rawBoundaries_truncate T p k hk (n+1) (by omega)]
  have h : min (n+1) (k+1) = min n k + 1 := by omega
  simp only [h]

private theorem rawInfinityBoundaries_finite (T : RawTower C) (p : ℤ × ℤ)
    (k : ℕ) (hk : p.1 = k) :
    allBoundaries T p ⊤ = finiteBoundaries T p k := by
  change (⨆ n, finiteBoundaries T p n) = finiteBoundaries T p k
  apply le_antisymm
  · apply iSup_le
    intro n
    rw [rawFiniteBoundaries_truncate T p k hk n]
    exact finiteBoundaries_monotone T p (by omega)
  · exact le_iSup (finiteBoundaries T p) k

private theorem rawBoundaries_zero_column (T : RawTower C) (p : ℤ × ℤ)
    (hp : p.1=0) (r : ℕ) (hr : 1 ≤ r) :
    T.boundaries r hr p = ⊥ := by
  rw [rawBoundaries_stabilize T p 0 hp r (by omega)]
  exact rawBoundaries_one T p

private theorem rawData_B_truncate (T : RawTower C) (p : ℤ × ℤ)
    (k : ℕ) (hk : p.1 = k) (n : ℕ) :
    (towerSSData T p).B n = (towerSSData T p).B ((min n k : ℕ) : WithTop ℕ) := by
  change (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm (finiteBoundaries T p n) =
    (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm (finiteBoundaries T p (min n k))
  rw [rawFiniteBoundaries_truncate T p k hk n]

private theorem rawData_B_top (T : RawTower C) (p : ℤ × ℤ)
    (k : ℕ) (hk : p.1 = k) :
    (towerSSData T p).B ⊤ = (towerSSData T p).B k := by
  change (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm (allBoundaries T p ⊤) =
    (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm (finiteBoundaries T p k)
  rw [rawInfinityBoundaries_finite T p k hk]

private theorem rawData_B_zero_column (T : RawTower C) (p : ℤ × ℤ)
    (hp : p.1=0) (n : WithTop ℕ) : (towerSSData T p).B n = ⊥ := by
  cases n with
  | top => rw [rawData_B_top T p 0 hp]; exact rawData_B_zero T p
  | coe n =>
    have h := rawData_B_truncate T p 0 hp n
    simp only [Nat.min_zero] at h
    exact h.trans (rawData_B_zero T p)

end
end KIP126.Literature.BocksteinRaw
end

@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private theorem lambdaData_B_truncate (X : Syn) (p : ℤ × ℤ × ℤ)
    (k : ℕ) (hk : p.2.1-p.2.2=k) (n : ℕ) :
    ((lambdaSequence X).ssData p).B n =
      ((lambdaSequence X).ssData p).B ((min n k : ℕ) : WithTop ℕ) := by
  exact rawData_B_truncate
    (lambdaTower ((SyntheticCategory.biShift (0,-p.2.2)).obj X))
    (lambdaGrading p) k hk n

private theorem lambdaData_B_top (X : Syn) (p : ℤ × ℤ × ℤ)
    (k : ℕ) (hk : p.2.1-p.2.2=k) :
    ((lambdaSequence X).ssData p).B ⊤ = ((lambdaSequence X).ssData p).B k := by
  exact rawData_B_top
    (lambdaTower ((SyntheticCategory.biShift (0,-p.2.2)).obj X))
    (lambdaGrading p) k hk

private theorem lambdaData_B_zero_diagonal (X : Syn) (s t : ℤ) (n : WithTop ℕ) :
    ((lambdaSequence X).ssData (s,t,t)).B n = ⊥ := by
  exact rawData_B_zero_column
    (lambdaTower ((SyntheticCategory.biShift (0,-t)).obj X))
    (lambdaGrading (s,t,t)) (by change t-t=0; omega) n

end
end KIP126.Literature.BocksteinRaw
end
