module
public import KIP126.Literature.Standard
public import KIP126.Literature.E2Exactness.Coordinates
import all KIP126.Literature.E2Exactness.SuspendedCoordinates
import all KIP126.Literature.Standard.FiniteQuotientNormalized

/-! The E₂ exact sequence of one compatible normalized cofiber triangle.
All three maps belong to the same selected Adams and first-quotient data. -/
@[expose] section
namespace KIP126.Literature.Standard.E2Exactness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
/-- The normalized first-quotient operation is an actual additive map. -/
public def e2ConnectingHom
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) :
    (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t) →+
      (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s+1,t+1) where
  toFun := e2Connecting T hf s t
  map_zero' := by
    simp only [e2Connecting,
      map_zero, zero_comp]
    have zero_regrade {A : SyntheticSpectrum} {m m' w w' : ℤ}
        (hm : m=m') (hw : w=w') :
        homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
      subst m'; subst w'; rfl
    rw [zero_regrade, map_zero]
  map_add' a b := by
    simp only [e2Connecting,
      map_add, Preadditive.add_comp]
    have add_regrade {A : SyntheticSpectrum} {m m' w w' : ℤ}
        (hm : m=m') (hw : w=w') (u v : BiHom m w A) :
        homotopyRegrade hm hw (u+v)=
          homotopyRegrade hm hw u+homotopyRegrade hm hw v := by
      subst m'; subst w'; rfl
    rw [add_regrade, map_add]
/-- The classical desuspension determined by the tower comparison. -/
private def classicalDesuspensionHom (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) :
    Ambient background (.shift 1 X) (s,t) →+
      Ambient background X (s,t-1) where
  toFun sx := Classical.choose (exists_desuspendsClass X s t sx)
  map_zero' := (desuspendsClass_eq_zero_iff X s t 0 _
    (Classical.choose_spec (exists_desuspendsClass X s t 0))).mp rfl
  map_add' sx sy := by
    exact (desuspendsClass_eq_iff X s t (sx+sy) (sx+sy) _ _
      (Classical.choose_spec (exists_desuspendsClass X s t (sx+sy)))
      (suspension_desuspends_add X s t sx sy _ _
        (Classical.choose_spec (exists_desuspendsClass X s t sx))
        (Classical.choose_spec (exists_desuspendsClass X s t sy)))).mp rfl

private theorem classicalDesuspensionHom_spec (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (sx : Ambient background (.shift 1 X) (s,t)) :
    (background.classicalSuspension X).DesuspendsClass s t sx
      (classicalDesuspensionHom X s t sx) :=
  Classical.choose_spec (exists_desuspendsClass X s t sx)

/-- The ordinary h₂ map followed by actual classical desuspension. -/
private def rawClassicalTriangleHMapHom
    (T : TriangleData background.auxiliary) (s t : ℤ) :
    Ambient background T.Z (s,t) →+
      Ambient background T.X (s,t-1) where
  toFun z := classicalDesuspensionHom T.X s t
    ((background.classical.map T.h).pageMap 2 (s,t) z)
  map_zero' := by rw [map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add]

private theorem rawClassicalTriangleHMapHom_spec
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) :
    (background.classicalSuspension T.X).DesuspendsClass s t
      ((background.classical.map T.h).pageMap 2 (s,t) z)
      (rawClassicalTriangleHMapHom T s t z) :=
  classicalDesuspensionHom_spec T.X s t _

/-- Exactness retains the actual quotient connecting arrow, including its
sign and the selected inclusion-compatible suspension comparison. -/
private theorem normalized_quotient_boundary_exact
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible background T he)
    (q : ℕ) (hq : 0<q) (m w : ℤ) :
    let N := KIP126.Literature.normalizedTriangle background T he
    ∀ a : BiHom m w (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q),
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 ↔
      ∃ b : BiHom m w (XModLambdaN N.obj₃ q),
        b ≫ XModLambdaN.map N.mor₃ q=a := by
  let N := KIP126.Literature.normalizedTriangle background T he
  obtain ⟨esusp, _, hrow⟩ :=
    KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he q hq
  let R := Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫ esusp.hom))
  dsimp only []
  intro a
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := Triangle.coyoneda_exact₃ R hrow a (by
      change a ≫ (-(_ ≫ esusp.hom))=0
      rw [Preadditive.comp_neg, ←Category.assoc, ha, zero_comp, neg_zero])
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,rfl⟩
    apply (cancel_mono esusp.hom).mp
    have hz := comp_distTriang_mor_zero₂₃ R hrow
    change XModLambdaN.map N.mor₃ q ≫ (-(_ ≫ esusp.hom))=0 at hz
    rw [Preadditive.comp_neg, neg_eq_zero] at hz
    simpa only [Category.assoc, comp_zero, zero_comp] using
      congrArg (fun f => b ≫ f) hz
/-- The actual ordinary E₂ map of h followed by desuspension in the
selected classical Adams tower. -/
private def classicalTriangleHMapHom
    (T : TriangleData background.auxiliary) (s t : ℤ) :
    Ambient background T.Z (s,t+1) →+ Ambient background T.X (s,t) := by
  exact (congrArg (fun u : ℤ => Ambient background T.Z (s,t+1) →+
      Ambient background T.X (s,u)) (show t+1-1=t by omega)).mp
    (rawClassicalTriangleHMapHom T s (t+1))

/-- The additive map above retains the original representative-level
meaning of the selected desuspension comparison. -/
private theorem classicalTriangleHMapHom_spec
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (z : Ambient background T.Z (s,t+1)) :
    (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z)
      (by simpa only [show t+1-1=t by omega] using classicalTriangleHMapHom T s t z) := by
  have undo (n n' : ℤ) (hn : n=n')
      (f : Ambient background T.Z (s,t+1) →+ Ambient background T.X (s,n)) :
      (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr
        (((congrArg (fun u : ℤ => Ambient background T.Z (s,t+1) →+
          Ambient background T.X (s,u)) hn).mp f) z)=f z := by
    subst n'; rfl
  change (background.classicalSuspension T.X).DesuspendsClass s (t+1)
    ((background.classical.map T.h).pageMap 2 (s,t+1) z)
    ((congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type))
      (show t+1-1=t by omega)).mpr
      (((congrArg (fun u : ℤ => Ambient background T.Z (s,t+1) →+
        Ambient background T.X (s,u)) (show t+1-1=t by omega)).mp
        (rawClassicalTriangleHMapHom T s (t+1))) z))
  rw [undo (t+1-1) t (by omega)]
  exact rawClassicalTriangleHMapHom_spec T s (t+1) z
/-- The exact row in suspended classical E₂ coordinates. -/
private theorem suspended_normalized_boundary_exact
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : KIP126.Literature.NormalizedTriangleCompatible background T he)
    (s t : ℤ) (sx : Ambient background (.shift 1 T.X) (s,t+1)) :
    let N := KIP126.Literature.normalizedTriangle background T he
    let E := normalizedSuspensionNativeIso T he hf
    (nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
      XModLambdaN.map E.inv 1) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1=0 ↔
    ∃ z : Ambient background T.Z (s,t+1),
      (background.classical.map T.h).pageMap 2 (s,t+1) z=sx := by
  dsimp only []
  let N := KIP126.Literature.normalizedTriangle background T he
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let Q := background.quotients.functoriality.functor 1
  have hmap : XModLambdaN.map N.mor₃ 1 ≫ XModLambdaN.map E.hom 1=
      XModLambdaN.map EZ.hom 1 ≫ XModLambdaN.map (background.nu.functor.map T.h) 1 := by
    rw [←background.quotients.functoriality.map_comp, ←background.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f 1)
      (normalized_third_arrow_zero T he hf hg hh)
  constructor
  · intro hzero
    obtain ⟨b,hb⟩ := (normalized_quotient_boundary_exact T he hT 1 (by omega)
      ((t+1)-s) (t+1) _).mp hzero
    obtain ⟨z,hz⟩ := nativeFirstLabel_surjective T.Z s (t+1)
      (b ≫ XModLambdaN.map EZ.hom 1)
    refine ⟨z, nativeFirstLabel_injective (.shift 1 T.X) s (t+1) ?_⟩
    rw [←native_first_label_natural, hz, Category.assoc, ←hmap,
      ←Category.assoc, hb]
    simp only [E, Category.assoc, ←background.quotients.functoriality.map_comp,
      Iso.inv_hom_id, background.quotients.functoriality.map_id, Category.comp_id]
  · rintro ⟨z, rfl⟩
    apply (normalized_quotient_boundary_exact T he hT 1 (by omega)
      ((t+1)-s) (t+1) _).mpr
    refine ⟨nativeFirstLabel T.Z s (t+1) z ≫ XModLambdaN.map EZ.inv 1, ?_⟩
    apply (cancel_mono (Q.mapIso E).hom).mp
    change _ ≫ XModLambdaN.map E.hom 1=_ ≫ XModLambdaN.map E.hom 1
    rw [Category.assoc, Category.assoc, hmap]
    simp only [E, Category.assoc, ←background.quotients.functoriality.map_comp,
      Iso.inv_hom_id, Iso.inv_hom_id_assoc, background.quotients.functoriality.map_id,
      Category.comp_id]
    exact native_first_label_natural T.Z (.shift 1 T.X) T.h s (t+1) z

private theorem classical_h_image_iff_suspended
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (sx : Ambient background (.shift 1 T.X) (s,t+1))
    (hsx : (background.classicalSuspension T.X).DesuspendsClass s (t+1) sx
      (by simpa only [show t+1-1=t by omega] using x)) :
    (∃ z : Ambient background T.Z (s,t+1),
      (background.classical.map T.h).pageMap 2 (s,t+1) z=sx) ↔
    ∃ z : Ambient background T.Z (s,t+1),
      classicalTriangleHMapHom T s t z=x := by
  have cast_eq (n n' : ℤ) (hn : n=n')
      (a b : Ambient background T.X (s,n')) :
      (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr a =
        (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr b ↔
      a=b := by
    subst n'; rfl
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z, ?_⟩
    have h := (desuspendsClass_eq_iff T.X s (t+1) _ sx _ _
      (classicalTriangleHMapHom_spec T s t z) hsx).mp hz
    exact (cast_eq (t+1-1) t (by omega) _ _).mp h
  · rintro ⟨z,hz⟩
    refine ⟨z, (desuspendsClass_eq_iff T.X s (t+1) _ sx _ _
      (classicalTriangleHMapHom_spec T s t z) hsx).mpr ?_⟩
    exact (cast_eq (t+1-1) t (by omega) _ _).mpr hz
/-- The E₂ kernel--image equation for the normalized quotient
operation induced by the compatible normalized triangle. -/
private theorem e2Connecting_exact
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : KIP126.Literature.NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (s t : ℤ) :
    (e2ConnectingHom T hf s t).ker=
      (classicalTriangleHMapHom T s t).range := by
  ext x
  change e2Connecting T hf s t x=0 ↔
    ∃ z, classicalTriangleHMapHom T s t z=x
  obtain ⟨sx,hsx⟩ := exists_suspendsClass T.X s (t+1)
    (by simpa only [show t+1-1=t by omega] using x)
  exact (cofiber_boundary_zero_iff_normalized_suspended_image
    T (by simp [hf,hg,hh]) hf s t x sx hsx).trans
    ((suspended_normalized_boundary_exact T (by simp [hf,hg,hh]) hf hg hh hT s t sx).trans
      (classical_h_image_iff_suspended T s t x sx hsx))

/-- Exactness at the source of the specified E₂ connecting operation.
Its kernel is the image of the h page map followed by the selected
Adams desuspension. The operation has bidegree (1,1). -/
public theorem e2ExactAtX
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (x : (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t)) :
    e2Connecting T hf s t x=0 ↔
      ∃ z : (background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s,t+1),
        (background.classicalSuspension T.X).DesuspendsClass s (t+1)
          ((background.classical.map T.h).pageMap 2 (s,t+1) z)
          (by simpa only [show t+1-1=t by omega] using x) := by
  have hT : KIP126.Literature.NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  have hexact : e2Connecting T hf s t x=0 ↔
      ∃ z, classicalTriangleHMapHom T s t z=x := by
    change x ∈ (e2ConnectingHom T hf s t).ker ↔
      x ∈ (classicalTriangleHMapHom T s t).range
    rw [e2Connecting_exact T hf hg hh hT s t]
  rw [hexact]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, classicalTriangleHMapHom_spec T s t z⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have heq := (desuspendsClass_eq_iff T.X s (t+1) _ _ _ _
      (classicalTriangleHMapHom_spec T s t z) hz).mp rfl
    have cast_injective (n n' : ℤ) (hn : n=n')
        (a b : Ambient background T.X (s,n'))
        (h : (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr a =
          (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr b) :
        a=b := by
      subst n'; exact h
    exact cast_injective (t+1-1) t (by omega) _ _ heq


/-- Exactness at the Z term for the ordinary g and h maps on the
classical E₂ page. -/
public theorem e2ExactAtZ
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (z : (background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s,t)) :
    (background.classical.map T.h).pageMap 2 (s,t) z=0 ↔
      ∃ y : (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s,t),
        (background.classical.map T.g).pageMap 2 (s,t) y=z := by
  let he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1 := by simp [hf,hg,hh]
  let N := KIP126.Literature.normalizedTriangle background T he
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let Q := background.quotients.functoriality.functor 1
  obtain ⟨esusp,_,hrow⟩ := normalized_finite_quotient_horizontal_row T he 1 (by omega)
  let R := Triangle.mk (XModLambdaN.map N.mor₂ 1) (XModLambdaN.map N.mor₃ 1)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1 ≫ esusp.hom))
  have hgmap : XModLambdaN.map N.mor₂ 1 ≫ XModLambdaN.map EZ.hom 1 =
      XModLambdaN.map (background.nu.functor.map T.g) 1 := by
    rw [←background.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f 1) (normalized_second_arrow_zero T he hg)
  have hhmap : XModLambdaN.map N.mor₃ 1 ≫ XModLambdaN.map E.hom 1 =
      XModLambdaN.map EZ.hom 1 ≫ XModLambdaN.map (background.nu.functor.map T.h) 1 := by
    rw [←background.quotients.functoriality.map_comp,←background.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f 1) (normalized_third_arrow_zero T he hf hg hh)
  let a := nativeFirstLabel T.Z s t z ≫ XModLambdaN.map EZ.inv 1
  have ha : a ≫ XModLambdaN.map N.mor₃ 1 = 0 ↔
      (background.classical.map T.h).pageMap 2 (s,t) z=0 := by
    have hcomp : (a ≫ XModLambdaN.map N.mor₃ 1) ≫ XModLambdaN.map E.hom 1 =
        nativeFirstLabel (.shift 1 T.X) s t ((background.classical.map T.h).pageMap 2 (s,t) z) := by
      dsimp only [a]
      rw [Category.assoc,Category.assoc,hhmap]
      simp only [←Category.assoc,←background.quotients.functoriality.map_comp,
        Iso.inv_hom_id,Category.id_comp]
      exact native_first_label_natural T.Z (.shift 1 T.X) T.h s t z
    rw [←native_label_zero_iff (.shift 1 T.X) s t,←hcomp]
    constructor
    · intro h; rw [h,zero_comp]
    · intro h
      apply (cancel_mono (Q.mapIso E).hom).mp
      change (a ≫ XModLambdaN.map N.mor₃ 1) ≫ XModLambdaN.map E.hom 1 =
        0 ≫ XModLambdaN.map E.hom 1
      simpa only [zero_comp] using h
  rw [←ha]
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := Triangle.coyoneda_exact₂ R hrow a hz
    change a = b ≫ XModLambdaN.map N.mor₂ 1 at hb
    obtain ⟨y,hy⟩ := nativeFirstLabel_surjective T.Y s t b
    refine ⟨y,nativeFirstLabel_injective T.Z s t ?_⟩
    rw [←native_first_label_natural,hy,←hgmap,←Category.assoc,←hb]
    simp only [a,Category.assoc,←background.quotients.functoriality.map_comp,
      Iso.inv_hom_id,background.quotients.functoriality.map_id,Category.comp_id]
  · rintro ⟨y,rfl⟩
    have hb : a = nativeFirstLabel T.Y s t y ≫ XModLambdaN.map N.mor₂ 1 := by
      apply (cancel_mono (Q.mapIso EZ).hom).mp
      change a ≫ XModLambdaN.map EZ.hom 1 =
        (nativeFirstLabel T.Y s t y ≫ XModLambdaN.map N.mor₂ 1) ≫ XModLambdaN.map EZ.hom 1
      dsimp only [a]
      rw [Category.assoc, ←background.quotients.functoriality.map_comp,
        Iso.inv_hom_id, background.quotients.functoriality.map_id, Category.comp_id,
        Category.assoc, hgmap]
      exact (native_first_label_natural T.Y T.Z T.g s t y).symm
    rw [hb,Category.assoc]
    have hz := comp_distTriang_mor_zero₁₂ R hrow
    change XModLambdaN.map N.mor₂ 1 ≫ XModLambdaN.map N.mor₃ 1 = 0 at hz
    simpa only [comp_zero] using congrArg (fun f => nativeFirstLabel T.Y s t y ≫ f) hz

private theorem source_label_surjective
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (b : BiHom ((t+1)-s) (t+1)
      (XModLambdaN ((KIP126.Literature.normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1)) :
    ∃ (x : Ambient background T.X (s,t)) (sx : Ambient background (.shift 1 T.X) (s,t+1)),
      (background.classicalSuspension T.X).DesuspendsClass s (t+1) sx
        (by simpa only [show t+1-1=t by omega] using x) ∧
      nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
        XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1 = b := by
  let E := normalizedSuspensionNativeIso T he hf
  obtain ⟨sx,hsx⟩ := nativeFirstLabel_surjective (.shift 1 T.X) s (t+1)
    (b ≫ XModLambdaN.map E.hom 1)
  obtain ⟨x0,hx0⟩ := exists_desuspendsClass T.X s (t+1) sx
  let hidx : t+1-1=t := by omega
  let hty := congrArg (fun n : ℤ => (Ambient background T.X (s,n) : Type)) hidx
  let x : Ambient background T.X (s,t) := hty.mp x0
  refine ⟨x,sx,?_,?_⟩
  · change (background.classicalSuspension T.X).DesuspendsClass s (t+1) sx (hty.mpr x)
    have undo {A B : Type} (h : A=B) (a : A) : h.mpr (h.mp a)=a := by
      subst B; rfl
    simpa only [x,undo] using hx0
  · rw [hsx,Category.assoc,←background.quotients.functoriality.map_comp,
      Iso.hom_inv_id,background.quotients.functoriality.map_id,Category.comp_id]

private theorem suspended_connecting_label
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (sx : Ambient background (.shift 1 T.X) (s,t+1))
    (hsx : (background.classicalSuspension T.X).DesuspendsClass s (t+1) sx
      (by simpa only [show t+1-1=t by omega] using x))
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ 1 ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (show (t+1)-s=t-s+1 by omega) rfl
      (((nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
        XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (KIP126.Literature.normalizedTriangle background T he).mor₁) 1) ≫ ey.hom) =
    ordinarySuspendedRepresentative _ (t-s+1) (t+1)
      (homotopyRegrade (show (t+1)-(s+1)=(t-s+1)-1 by omega) rfl
        (nativeFirstLabel T.Y (s+1) (t+1) (e2Connecting T hf s t x))) := by
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε⟩ := finite_quotient_shift_comparison background.quotients.coherence (1,1) 1
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  rw [cofiberFirstQuotientBoundary_native_label,normalized_homotopy_regrade_trans]
  exact normalized_suspended_image_coordinates T he hf s t x sx hsx ε hε ey hey

private theorem normalized_suspended_middle_exact
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1)
    (_hT : KIP126.Literature.NormalizedTriangleCompatible background T he)
    (esusp : XModLambdaN (((KIP126.Literature.normalizedTriangle background T he).obj₂)⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (KIP126.Literature.normalizedTriangle background T he).obj₂ 1)⟦(1:ℤ)⟧)
    (hrow : let N := KIP126.Literature.normalizedTriangle background T he
      Triangle.mk (XModLambdaN.map N.mor₂ 1) (XModLambdaN.map N.mor₃ 1)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1 ≫ esusp.hom)) ∈
          distTriang SyntheticSpectrum)
    (m w : ℤ) (a : BiHom m w
      ((XModLambdaN (KIP126.Literature.normalizedTriangle background T he).obj₂ 1)⟦(1:ℤ)⟧)) :
    a ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.map (KIP126.Literature.normalizedTriangle background T he).mor₂ 1)=0 ↔
    ∃ b : BiHom m w (XModLambdaN
        ((KIP126.Literature.normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1),
      b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (KIP126.Literature.normalizedTriangle background T he).mor₁) 1 ≫ esusp.hom=a := by
  let N := KIP126.Literature.normalizedTriangle background T he
  let R := Triangle.mk (XModLambdaN.map N.mor₂ 1) (XModLambdaN.map N.mor₃ 1)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1 ≫ esusp.hom))
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := Triangle.coyoneda_exact₃ R.rotate (rot_of_distTriang R hrow) a (by
      change a ≫ (-(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map N.mor₂ 1))=0
      rw [Preadditive.comp_neg,ha,neg_zero])
    refine ⟨-b,?_⟩
    change a = b ≫ (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1 ≫ esusp.hom)) at hb
    simpa only [Preadditive.neg_comp,Preadditive.comp_neg] using hb.symm
  · rintro ⟨b,rfl⟩
    have hz := comp_distTriang_mor_zero₃₁ R hrow
    change (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1 ≫ esusp.hom)) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map N.mor₂ 1)=0 at hz
    rw [Preadditive.neg_comp,neg_eq_zero] at hz
    simpa only [Category.assoc,comp_zero] using congrArg (fun f => b ≫ f) hz

private def suspendedTargetLabel (Y : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (y : Ambient background Y (s+1,t+1)) :
    BiHom (t-s+1) (t+1) ((XModLambdaN
      (background.nu.functor.obj (Y.obj background.auxiliary)) 1)⟦(1:ℤ)⟧) :=
  ordinarySuspendedRepresentative _ (t-s+1) (t+1)
    (homotopyRegrade (show (t+1)-(s+1)=(t-s+1)-1 by omega) rfl
      (nativeFirstLabel Y (s+1) (t+1) y))

private theorem suspendedTargetLabel_injective (Y : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) :
    Function.Injective (suspendedTargetLabel Y s t) := by
  intro a b h
  apply nativeFirstLabel_injective Y (s+1) (t+1)
  apply homotopy_regrade_injective (show (t+1)-(s+1)=(t-s+1)-1 by omega) (rfl : t+1=t+1)
  exact ordinary_suspended_representative_injective _ (t-s+1) (t+1) h

private theorem suspendedTargetLabel_kernel
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1)
    (hg : normalizedExponent background.classicalTower T.g=0) (s t : ℤ)
    (y : Ambient background T.Y (s+1,t+1)) :
    suspendedTargetLabel T.Y s t y ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.map (KIP126.Literature.normalizedTriangle background T he).mor₂ 1)=0 ↔
      (background.classical.map T.g).pageMap 2 (s+1,t+1) y=0 := by
  let N := KIP126.Literature.normalizedTriangle background T he
  let EZ := normalizedThirdZeroIso T he hg
  let Q := background.quotients.functoriality.functor 1
  have hgmap : XModLambdaN.map N.mor₂ 1 ≫ XModLambdaN.map EZ.hom 1 =
      XModLambdaN.map (background.nu.functor.map T.g) 1 := by
    rw [←background.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f 1) (normalized_second_arrow_zero T he hg)
  have hn : nativeFirstLabel T.Y (s+1) (t+1) y ≫ XModLambdaN.map N.mor₂ 1=0 ↔
      (background.classical.map T.g).pageMap 2 (s+1,t+1) y=0 := by
    rw [←native_label_zero_iff T.Z (s+1) (t+1),←native_first_label_natural]
    rw [←hgmap,←Category.assoc]
    constructor
    · intro h; rw [h,zero_comp]
    · intro h
      apply (cancel_mono (Q.mapIso EZ).hom).mp
      change _ ≫ XModLambdaN.map EZ.hom 1 = 0 ≫ XModLambdaN.map EZ.hom 1
      simpa only [zero_comp] using h
  rw [←hn]
  unfold suspendedTargetLabel
  rw [←ordinarySuspendedRepresentative_natural,←regrade_comp]
  constructor
  · intro h
    have h' := ordinary_suspended_representative_injective _ (t-s+1) (t+1)
      (h.trans (ordinary_suspended_zero _ _ _).symm)
    apply homotopy_regrade_injective (show (t+1)-(s+1)=(t-s+1)-1 by omega) (rfl : t+1=t+1)
    simpa only [regrade_zero] using h'
  · intro h
    rw [h,regrade_zero,ordinary_suspended_zero]

/-- Exactness at the Y term: the kernel of the actual g₂ is the image
of the same normalized first-quotient connecting map of bidegree (1,1). -/
public theorem e2ExactAtY
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (y : (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s+1,t+1)) :
    (background.classical.map T.g).pageMap 2 (s+1,t+1) y=0 ↔
      ∃ x : (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t),
        e2Connecting T hf s t x=y := by
  have hT : KIP126.Literature.NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+
      normalizedExponent background.classicalTower T.h=1 := by simp [hf,hg,hh]
  let N := KIP126.Literature.normalizedTriangle background T he
  obtain ⟨esusp,hesusp,hrow⟩ := normalized_finite_quotient_horizontal_row T he 1 (by omega)
  have hex := normalized_suspended_middle_exact T he hT esusp hrow
    (t-s+1) (t+1) (suspendedTargetLabel T.Y s t y)
  rw [←suspendedTargetLabel_kernel T he hg s t y,hex]
  constructor
  · rintro ⟨b,hb⟩
    let br := homotopyRegrade (show t-s+1=(t+1)-s by omega) (rfl : t+1=t+1) b
    obtain ⟨x,sx,hsx,hbx⟩ := source_label_surjective T he hf s t br
    refine ⟨x,suspendedTargetLabel_injective T.Y s t ?_⟩
    have H := suspended_connecting_label T he hf s t x sx hsx esusp hesusp
    rw [hbx] at H
    have hbr : homotopyRegrade (show (t+1)-s=t-s+1 by omega) (rfl : t+1=t+1)
        ((br ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1) ≫ esusp.hom) =
        b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1 ≫ esusp.hom := by
      simp only [br,regrade_comp,normalized_homotopy_regrade_trans,Category.assoc]
      rfl
    rw [hbr,hb] at H
    exact H.symm
  · rintro ⟨x,rfl⟩
    obtain ⟨sx,hsx⟩ := exists_suspendsClass T.X s (t+1)
      (by simpa only [show t+1-1=t by omega] using x)
    let b := homotopyRegrade (show (t+1)-s=t-s+1 by omega) (rfl : t+1=t+1)
      (nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
        XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1)
    refine ⟨b,?_⟩
    have H := suspended_connecting_label T he hf s t x sx hsx esusp hesusp
    simpa only [b,suspendedTargetLabel,regrade_comp,Category.assoc] using H

/-- The complete E₂ long exact sequence of the specified normalized
triangle. Quantifying over all bidegrees joins these three consecutive
kernel--image equations. The h map is the actual ordinary page map, with
its selected classical desuspension at the X term; δ has degree (1,1).
The normalization and compatibility hypotheses concern this same triangle. -/
public theorem e2LongExactSequence
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) :
    (∀ x : (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t),
      e2Connecting T hf s t x=0 ↔
        ∃ z : (background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s,t+1),
          (background.classicalSuspension T.X).DesuspendsClass s (t+1)
            ((background.classical.map T.h).pageMap 2 (s,t+1) z)
            (by simpa only [show t+1-1=t by omega] using x)) ∧
    (∀ y : (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s+1,t+1),
      (background.classical.map T.g).pageMap 2 (s+1,t+1) y=0 ↔
        ∃ x : (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t),
          e2Connecting T hf s t x=y) ∧
    (∀ z : (background.classical.obj (T.Z.obj background.auxiliary)).Page 2 (s+1,t+1),
      (background.classical.map T.h).pageMap 2 (s+1,t+1) z=0 ↔
        ∃ y : (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s+1,t+1),
          (background.classical.map T.g).pageMap 2 (s+1,t+1) y=z) := by
  exact ⟨e2ExactAtX T hf hg hh s t,
    e2ExactAtY T hf hg hh s t,
    e2ExactAtZ T hf hg hh (s+1) (t+1)⟩

end
end KIP126.Literature.Standard.E2Exactness
