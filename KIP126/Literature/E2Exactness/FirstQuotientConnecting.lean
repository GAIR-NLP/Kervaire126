module
import all KIP126.Literature.E2Exactness.SuspendedCoordinates
import all KIP126.Literature.Standard.FiniteQuotientTriangle

/-! Uniform first-quotient connecting maps and represented-Hom exactness. -/
@[expose] section
namespace KIP126.Literature.Standard.E2Exactness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.Literature.Standard.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
theorem homotopy_regrade_add {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a b : BiHom m w A) :
    homotopyRegrade hm hw (a+b)=homotopyRegrade hm hw a+homotopyRegrade hm hw b := by
  subst m'; subst w'; rfl

def nativeLabelAddEquiv (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) :
    Ambient background X (s,t) ≃+
      BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
  let f : Ambient background X (s,t) →+
      BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
    { toFun := nativeFirstLabel X s t
      map_zero' := (native_label_zero_iff X s t 0).mpr rfl
      map_add' := by
        intro a b
        simp only [nativeFirstLabel_eq_regrade, map_add,
          homotopy_regrade_add,Preadditive.add_comp] }
  AddEquiv.ofBijective f
    ⟨nativeFirstLabel_injective X s t,nativeFirstLabel_surjective X s t⟩

def postcompIsoAddEquiv {A B : SyntheticSpectrum} (e : A ≅ B) (m w : ℤ) :
    BiHom m w A ≃+ BiHom m w B where
  toFun a := a ≫ e.hom
  invFun b := b ≫ e.inv
  left_inv a := by simp
  right_inv b := by simp
  map_add' a b := by simp only [Preadditive.add_comp]

def ordinarySuspendedAddEquiv (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) w A ≃+ BiHom m w (A⟦(1:ℤ)⟧) :=
  (suspInvarianceAddEquiv (m-1) w 1 0 A).trans
    ((regradeAddEquiv (show m-1+1=m by omega) (show w+0=w by omega)).trans
      (postcompIsoAddEquiv ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app A) m w))

theorem ordinarySuspendedAddEquiv_apply (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) w A) :
    ordinarySuspendedAddEquiv A m w a = ordinarySuspendedRepresentative A m w a := by
  change homotopyRegrade _ _
      ((SyntheticCategory.biShift_comp (m-1,w) (1,0)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (1,0)).map a ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  rfl

def e2SuspendedLabel (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) :
    Ambient background X (s+1,t) ≃+
      BiHom (t-s) t ((XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧) :=
  (nativeLabelAddEquiv X (s+1) t).trans
    ((regradeAddEquiv (show t-(s+1)=(t-s)-1 by omega) rfl).trans
      (ordinarySuspendedAddEquiv _ (t-s) t))

theorem e2SuspendedLabel_natural
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s+1,t)) :
    e2SuspendedLabel X s t x ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (XModLambdaN.map (background.nu.functor.map f) 1) =
      e2SuspendedLabel Y s t ((background.classical.map f).pageMap 2 (s+1,t) x) := by
  simp only [e2SuspendedLabel,AddEquiv.trans_apply,ordinarySuspendedAddEquiv_apply]
  rw [←ordinarySuspendedRepresentative_natural]
  change ordinarySuspendedRepresentative _ (t-s) t
      (homotopyRegrade _ rfl (nativeFirstLabel X (s+1) t x) ≫ _) =
    ordinarySuspendedRepresentative _ (t-s) t
      (homotopyRegrade _ rfl (nativeFirstLabel Y (s+1) t _))
  erw [←regrade_comp,native_first_label_natural X Y f (s+1) t x]
  all_goals rfl

/-- Connecting operation of the *given* actual ν triangle and the actual
quotient suspension comparison. Its degree is (1,0). -/
def hsesConnectingHom
    (T : TriangleData background.auxiliary)
    (δ : background.nu.functor.obj (T.Z.obj background.auxiliary) ⟶
      (background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧)
    (ε : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧)
    (s t : ℤ) : Ambient background T.Z (s,t) →+ Ambient background T.X (s+1,t) :=
  let c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) 1) →+
      BiHom (t-s) t ((XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧) :=
    { toFun := fun a => a ≫ XModLambdaN.map δ 1 ≫ ε.hom
      map_zero' := by simp
      map_add' := by intro a b; simp only [Preadditive.add_comp] }
  (e2SuspendedLabel T.X s t).symm.toAddMonoidHom.comp
    (c.comp (nativeLabelAddEquiv T.Z s t).toAddMonoidHom)


theorem hsesConnectingHom_label
    (T : TriangleData background.auxiliary)
    (δ : background.nu.functor.obj (T.Z.obj background.auxiliary) ⟶
      (background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧)
    (ε : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧)
    (s t : ℤ) (z : Ambient background T.Z (s,t)) :
    e2SuspendedLabel T.X s t (hsesConnectingHom T δ ε s t z) =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map δ 1 ≫ ε.hom := by
  change (e2SuspendedLabel T.X s t) ((e2SuspendedLabel T.X s t).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

theorem hses_exact_at_Y
    (T : TriangleData background.auxiliary)
    (δ : background.nu.functor.obj (T.Z.obj background.auxiliary) ⟶
      (background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧)
    (ε : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧)
    (hR : Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) 1)
      (XModLambdaN.map (background.nu.functor.map T.g) 1)
      (XModLambdaN.map δ 1 ≫ ε.hom) ∈ distTriang SyntheticSpectrum)
    (s t : ℤ) (y : Ambient background T.Y (s,t)) :
    (background.classical.map T.g).pageMap 2 (s,t) y = 0 ↔
      ∃ x : Ambient background T.X (s,t), (background.classical.map T.f).pageMap 2 (s,t) x = y := by
  let R := Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) 1)
    (XModLambdaN.map (background.nu.functor.map T.g) 1) (XModLambdaN.map δ 1 ≫ ε.hom)
  erw [←native_label_zero_iff T.Z s t,←native_first_label_natural T.Y T.Z T.g s t y]
  constructor
  · intro hy
    obtain ⟨a,ha⟩ := Triangle.coyoneda_exact₂ R hR (nativeFirstLabel T.Y s t y) hy
    obtain ⟨x,hx⟩ := nativeFirstLabel_surjective T.X s t a
    refine ⟨x,nativeFirstLabel_injective T.Y s t ?_⟩
    erw [←native_first_label_natural T.X T.Y T.f s t x,hx]
    exact ha.symm
  · rintro ⟨x,rfl⟩
    erw [←native_first_label_natural T.X T.Y T.f s t x,Category.assoc]
    have hz := comp_distTriang_mor_zero₁₂ R hR
    change XModLambdaN.map (background.nu.functor.map T.f) 1 ≫
      XModLambdaN.map (background.nu.functor.map T.g) 1 = 0 at hz
    rw [hz,comp_zero]

theorem hses_exact_at_Z
    (T : TriangleData background.auxiliary)
    (δ : background.nu.functor.obj (T.Z.obj background.auxiliary) ⟶
      (background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧)
    (ε : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧)
    (hR : Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) 1)
      (XModLambdaN.map (background.nu.functor.map T.g) 1)
      (XModLambdaN.map δ 1 ≫ ε.hom) ∈ distTriang SyntheticSpectrum)
    (s t : ℤ) (z : Ambient background T.Z (s,t)) :
    hsesConnectingHom T δ ε s t z = 0 ↔
      ∃ y : Ambient background T.Y (s,t), (background.classical.map T.g).pageMap 2 (s,t) y = z := by
  let R := Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) 1)
    (XModLambdaN.map (background.nu.functor.map T.g) 1) (XModLambdaN.map δ 1 ≫ ε.hom)
  have hz : e2SuspendedLabel T.X s t (hsesConnectingHom T δ ε s t z)=0 ↔
      hsesConnectingHom T δ ε s t z=0 := (e2SuspendedLabel T.X s t).map_eq_zero_iff
  rw [←hz,hsesConnectingHom_label]
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := Triangle.coyoneda_exact₃ R hR (nativeFirstLabel T.Z s t z) hz
    obtain ⟨y,hy⟩ := nativeFirstLabel_surjective T.Y s t b
    refine ⟨y,nativeFirstLabel_injective T.Z s t ?_⟩
    erw [←native_first_label_natural T.Y T.Z T.g s t y,hy]
    exact hb.symm
  · rintro ⟨y,rfl⟩
    erw [←native_first_label_natural T.Y T.Z T.g s t y,Category.assoc]
    have hz := comp_distTriang_mor_zero₂₃ R hR
    change XModLambdaN.map (background.nu.functor.map T.g) 1 ≫
      (XModLambdaN.map δ 1 ≫ ε.hom) = 0 at hz
    rw [hz,comp_zero]

theorem hses_exact_at_X
    (T : TriangleData background.auxiliary)
    (δ : background.nu.functor.obj (T.Z.obj background.auxiliary) ⟶
      (background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧)
    (ε : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1)⟦(1:ℤ)⟧)
    (hR : Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) 1)
      (XModLambdaN.map (background.nu.functor.map T.g) 1)
      (XModLambdaN.map δ 1 ≫ ε.hom) ∈ distTriang SyntheticSpectrum)
    (s t : ℤ) (x : Ambient background T.X (s+1,t)) :
    (background.classical.map T.f).pageMap 2 (s+1,t) x = 0 ↔
      ∃ z : Ambient background T.Z (s,t), hsesConnectingHom T δ ε s t z = x := by
  let R := Triangle.mk (XModLambdaN.map (background.nu.functor.map T.f) 1)
    (XModLambdaN.map (background.nu.functor.map T.g) 1) (XModLambdaN.map δ 1 ≫ ε.hom)
  have hx : e2SuspendedLabel T.Y s t ((background.classical.map T.f).pageMap 2 (s+1,t) x)=0 ↔
      (background.classical.map T.f).pageMap 2 (s+1,t) x=0 :=
    (e2SuspendedLabel T.Y s t).map_eq_zero_iff
  rw [←hx,←e2SuspendedLabel_natural]
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := Triangle.coyoneda_exact₃ R.rotate (rot_of_distTriang R hR)
      (e2SuspendedLabel T.X s t x) (by
        change e2SuspendedLabel T.X s t x ≫
          (-((shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (XModLambdaN.map (background.nu.functor.map T.f) 1)))=0
        rw [Preadditive.comp_neg,hx,neg_zero])
    obtain ⟨z,hz⟩ := nativeFirstLabel_surjective T.Z s t b
    refine ⟨z,(e2SuspendedLabel T.X s t).injective ?_⟩
    rw [hsesConnectingHom_label,hz]
    exact hb.symm
  · rintro ⟨z,rfl⟩
    rw [hsesConnectingHom_label,Category.assoc]
    have hz := comp_distTriang_mor_zero₃₁ R hR
    change (XModLambdaN.map δ 1 ≫ ε.hom) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map (background.nu.functor.map T.f) 1)=0 at hz
    rw [hz,comp_zero]


end
end KIP126.Literature.Standard.E2Exactness
