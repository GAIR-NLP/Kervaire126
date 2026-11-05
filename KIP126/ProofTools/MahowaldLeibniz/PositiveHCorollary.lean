module
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHCore
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryImageSquare
import all KIP126.ProofTools.MahowaldLeibniz.TerminalOrdinary
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeLabels

/-! Classical composition with positive third exponent, derived from the common finite core. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem positive_h_regrade_self {A : SyntheticSpectrum} {m w : ℤ}
    (hm : m=m) (hw : w=w) (a : BiHom m w A) : homotopyRegrade hm hw a=a := by rfl

private theorem ordinary_boundary_image_decode_general
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (p : ℕ) (hp : 0<p) (s t S V m w : ℤ)
    (hS : S=s+p+1) (hV : V=t+p) (hm : m=t-s) (hw : w=t+(1:ℕ))
    (x : Ambient background T.X (s,t)) (v : Ambient background T.Y (S,V))
    (ex : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) p)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) p)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ p ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (hey : XModLambdaN.incl _ p ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (b : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) p))
    (hb : Detects (background.convergence (.quotient p (.nu T.Y))) (S,V,w)
      ((background.family.quotientProjection (background.nu.functor.obj (T.Y.obj background.auxiliary)) p).pageMap
        2 (S,V,w) (nuWeightLabel background T.Y S V w (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl b))
    (himage : ordinaryNormalizedFirstFiniteBoundary T he hf p hp s t ex x ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) p ≫ ey.hom =
      homotopyRegrade hm hw (ordinarySuspendedRepresentative _ m w b)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y p (s,t) y ∧ DifferentialAt background T.Y (p+1) (s,t) (S,V) y v := by
  subst S V m w
  exact ordinary_normalized_boundary_image_decode T he hf p hp s t x v ex ey hex hey b hb himage

private theorem positive_h_pdf_classical_corollary
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient background T.Z (s+(c+1),t+(c+1)))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+(c+1)) (t+(c+1)) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1),t+(c+1)) ((s+(c+1))+q+1,(t+(c+1))+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      cycles background T.X (((q+1:ℕ):ℤ)-j) ((s+(c+1))+1+j,(t+(c+1))+j) ≤
        boundaries background T.X ((c:ℤ)+j+1) ((s+(c+1))+1+j,(t+(c+1))+j))
    (hNC2 : ∀ a : Ambient background T.X
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1),
      (background.classical.map T.f).pageMap 2
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1) a ∈
        boundaries background T.Y (c+(q+1))
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let S := s+(c+1)
  let V := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.X.obj background.auxiliary)) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=V-S by dsimp [S,V]; omega)
    (show t+(1:ℕ)=V-c by dsimp [V]; omega)
    (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := ordinary_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  obtain ⟨a,ha,himage,hcycle,hunique⟩ := positive_third_finite_core T he hT hf hg hh
    c q hq S V z u v hu hdz ey hey ε hε
  have hA : ∀ e : BiHom (V-S) (V-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N),
      FiltrationAtLeast background.syntheticTower ((S+1)+1)
        (positiveHSourceDesuspend T he hf N c S V ε e) →
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) N=0 := by
    intro e he
    apply native_ordinary_image_zero_implies_raw_zero T _ hf N c hN S V ε hε e
    exact ordinary_map_pdf_annihilation T.X T.Y T.f c (q+1) (by omega) (S+1) V
      hNC1 hNC2 _ he
  have hda := hunique hA d hd
  have himageD := hda.trans himage
  obtain ⟨b,hb,hbimage⟩ := finite_may_signed_target_at_level T.Y c q hq S V v ey eY hey heY
  apply ordinary_boundary_image_decode_general T he hf N hN s t (S+q+1) (V+q)
    (V-S) (V-c) (by dsimp [S,N]; omega) (by dsimp [V,N]; omega)
    (by dsimp [S,V]; omega) (by dsimp [V]; omega) x v ex eY hex heY b hb
  apply homotopy_regrade_injective (show t-s=V-S by dsimp [S,V]; omega)
    (show t+(1:ℕ)=V-c by dsimp [V]; omega)
  have hi := congrArg (fun a => a ≫ eY.hom) himageD
  dsimp only [normalizedTriangle,Triangle.mk] at hi
  rw [hbimage] at hi
  simpa only [d,homotopyRegrade_comp,normalized_homotopy_regrade_trans,Category.assoc,
    normalizedTriangle,Triangle.mk,positive_h_regrade_self] using hi

private def PositiveHLabelRelated
    (T : TriangleData background.auxiliary)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (z : Ambient background T.Z (s,t)) {α : Type} (w : α) : Prop :=
  HEq w (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)

private theorem positive_h_pdf_classical_corollary_heq
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient background T.Z (s+(c+1),t+(c+1)))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : ∃ w : Ambient background (.shift 1 T.X) ((s+(c+1))+1,(t+(c+1))+1),
      ∃ u' : Ambient background T.X ((s+(c+1))+1,((t+(c+1))+1)-1),
      (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1) w u' ∧
      PositiveHLabelRelated T hh (s+(c+1)) (t+(c+1)) z w ∧ HEq u' u)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1),t+(c+1)) ((s+(c+1))+q+1,(t+(c+1))+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      cycles background T.X (((q+1:ℕ):ℤ)-j) ((s+(c+1))+1+j,(t+(c+1))+j) ≤
        boundaries background T.X ((c:ℤ)+j+1) ((s+(c+1))+1+j,(t+(c+1))+j))
    (hNC2 : ∀ a : Ambient background T.X
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1),
      (background.classical.map T.f).pageMap 2
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1) a ∈
        boundaries background T.Y (c+(q+1))
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  obtain ⟨w,u',hu',hW,hU⟩ := hu
  apply positive_h_pdf_classical_corollary T he hT hf hg hh c q hq s t x u z v ?_ hdx hdz hNC1 hNC2
  let uc : Ambient background T.X ((s+(c+1))+1,((t+(c+1))+1)-1) := by simpa using u
  have hc : HEq uc u := cast_heq _ _
  have heq : u'=uc := eq_of_heq (hU.trans hc.symm)
  have hw : w = positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
      (s+(c+1)) (t+(c+1)) z := eq_of_heq hW
  change (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
    (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
      (s+(c+1)) (t+(c+1)) z) uc
  rw [←heq,←hw]
  exact hu'

private theorem positive_h_pdf_classical_corollary_RK
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (R K : ℕ) (hR : 2≤R) (hK : 2≤K) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+R,t+R-1))
    (z : Ambient background T.Z (s+R-1,t+R-1))
    (v : Ambient background T.Y (s+R+K-1,t+R+K-2))
    (w : Ambient background (.shift 1 T.X) (s+R,t+R))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R) w u)
    (hw : PositiveHLabelRelated T hh (s+R-1) (t+R-1) z w)
    (hdx : DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt background T.Z K (s+R-1,t+R-1) (s+R+K-1,t+R+K-2) z
      ((background.classical.map T.g).pageMap 2 (s+R+K-1,t+R+K-2) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<K-1 →
      cycles background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries background T.X ((R:ℤ)+j-1) (s+R+j,t+R+j-1))
    (hNC2 : ∀ a : Ambient background T.X (s+R+K-1,t+R+K-2),
      (background.classical.map T.f).pageMap 2 (s+R+K-1,t+R+K-2) a ∈
      boundaries background T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y ((R:ℤ)+K-2) (s,t) y ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1) (s,t) (s+R+K-1,t+R+K-2) y v := by
  obtain ⟨c,rfl⟩ : ∃ c : ℕ, R=c+2 := ⟨R-2,by omega⟩
  obtain ⟨q,rfl⟩ : ∃ q : ℕ, K=q+1 := ⟨K-1,by omega⟩
  have Hst := positive_h_pdf_classical_corollary_heq T he hT hf hg hh c q (by omega) s t
  erw [show (s+((c:ℤ)+1))+q+1=s+(c+2:ℕ)+(q+1:ℕ)-1 by omega,
    show (t+((c:ℤ)+1))+q=t+(c+2:ℕ)+(q+1:ℕ)-2 by omega,
    show s+((c:ℤ)+1)+1=s+(c+2:ℕ) by omega,
    show (t+((c:ℤ)+1))+1=t+(c+2:ℕ) by omega,
    show s+((c:ℤ)+1)=s+(c+2:ℕ)-1 by omega,
    show t+((c:ℤ)+1)=t+(c+2:ℕ)-1 by omega] at Hst
  erw [show ((c:ℤ)+1)+1=(c+2:ℕ) by omega,
    show ((c:ℤ)+((q:ℤ)+1)+1)=(c+2:ℕ)+(q+1:ℕ)-1 by omega,
    show ((c:ℤ)+((q:ℤ)+1))=(c+2:ℕ)+(q+1:ℕ)-2 by omega,
    show (t+(c+2:ℕ)-1)+(q+1:ℕ)-1=t+(c+2:ℕ)+(q+1:ℕ)-2 by omega] at Hst
  have hind (j : ℕ) : (t+(c+2:ℕ)-1)+j=t+(c+2:ℕ)+j-1 := by omega
  have hbound (j : ℕ) : (c:ℤ)+j+1=(c+2:ℕ)+j-1 := by omega
  apply Hst x u z v ⟨w,u,hu,hw,HEq.rfl⟩ hdx.2 hdz.2 ?_ hNC2
  intro j hj hJ
  erw [hind j,hbound j]
  exact hNC1 j hj hJ

private theorem positive_h_classical_label_regrade_heq {X : AdamsObject (coefficients := background.coefficients)} {p q : ℤ×ℤ}
    (h : p=q) (x : Ambient background X p) : HEq (classicalLabelRegrade h x) x := by
  subst q
  rfl

private theorem positive_h_classical_map_label_heq (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient background X p) (b : Ambient background X q)
    (hab : HEq a b) :
    HEq ((background.classical.map f).pageMap 2 p a)
      ((background.classical.map f).pageMap 2 q b) := by
  subst q
  cases eq_of_heq hab
  rfl

private theorem positive_h_classical_cycle_heq (X : AdamsObject (coefficients := background.coefficients)) (r : ℤ)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient background X p) (b : Ambient background X q)
    (hab : HEq a b) (ha : IsCycle background X r p a) : IsCycle background X r q b := by
  subst q
  cases eq_of_heq hab
  exact ha

private theorem positive_h_classical_boundary_heq (X : AdamsObject (coefficients := background.coefficients)) (r : ℤ)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient background X p) (b : Ambient background X q)
    (hab : HEq a b) (ha : a ∈ boundaries background X r p) : b ∈ boundaries background X r q := by
  subst q
  cases eq_of_heq hab
  exact ha

private theorem positive_h_classical_differential_heq (X : AdamsObject (coefficients := background.coefficients)) (r : ℤ)
    {p p' q q' : ℤ×ℤ} (hp : p=p') (hq : q=q')
    (a : Ambient background X p) (a' : Ambient background X p')
    (b : Ambient background X q) (b' : Ambient background X q')
    (ha : HEq a a') (hb : HEq b b')
    (hd : DifferentialAt background X r p q a b) :
    DifferentialAt background X r p' q' a' b' := by
  subst p' q'
  cases eq_of_heq ha
  cases eq_of_heq hb
  exact hd

private theorem positive_h_normalized_operation_zero_heq (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (hf : normalizedExponent background.classicalTower f = 0)
    (s t : ℤ) (x : Ambient background X (s,t)) :
    HEq (normalizedClassicalOperation X Y f s t x)
      ((background.classical.map f).pageMap 2 (s,t) x) :=
  (positive_h_classical_label_regrade_heq _ _).symm.trans
    (heq_of_eq (normalized_classical_operation_zero X Y f hf s t x))


private theorem positive_h_operation_heq
    (T : TriangleData background.auxiliary)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t s' t' : ℤ) (hs : s=s') (ht : t=t')
    (z : Ambient background T.Z (s,t)) (z' : Ambient background T.Z (s',t'))
    (hzz : HEq z z') :
    HEq (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s' t' z') := by
  subst s' t'
  cases eq_of_heq hzz
  rfl

private theorem positive_h_classical_nc_statement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1) :
    ClassicalNCCompositionStatement T he := by
  have hT := KIP126.Literature.Standard.normalized_triangle_distinguished T he
  intro R K hR hK s t x z v hx hz hu hdz hNC1 hNC2
  have hzdeg : (s+R-normalizedExponent background.classicalTower T.h,
      t+R-normalizedExponent background.classicalTower T.h)=(s+R-1,t+R-1) := by simp only [hh,Nat.cast_one]
  have hvdeg : (s+R+normalizedExponent background.classicalTower T.f+K-1,
      t+R+normalizedExponent background.classicalTower T.f+K-2)=(s+R+K-1,t+R+K-2) := by
    simp only [hf,Nat.cast_zero,add_zero]
  let z0 := classicalLabelRegrade hzdeg z
  let v0 := classicalLabelRegrade hvdeg v
  have hz0 : HEq z z0 := (positive_h_classical_label_regrade_heq hzdeg z).symm
  have hv0 : HEq v v0 := (positive_h_classical_label_regrade_heq hvdeg v).symm
  obtain ⟨u,hu,hdx⟩ := hu
  let w := classicalLabelRegrade (X := .shift 1 T.X) (q := (s+R,t+R))
    (by ext <;> dsimp <;> omega)
    (normalizedClassicalOperation T.Z (.shift 1 T.X) T.h
      (s+R-normalizedExponent background.classicalTower T.h)
      (t+R-normalizedExponent background.classicalTower T.h) z)
  have hhop : HEq (normalizedClassicalOperation T.Z (.shift 1 T.X) T.h
      (s+R-normalizedExponent background.classicalTower T.h)
      (t+R-normalizedExponent background.classicalTower T.h) z)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+R-normalizedExponent background.classicalTower T.h)
        (t+R-normalizedExponent background.classicalTower T.h) z) :=
    (positive_h_classical_label_regrade_heq _ _).symm.trans
      (heq_of_eq (normalized_classical_operation_one T.Z (.shift 1 T.X) T.h hh _ _ z))
  have hw : PositiveHLabelRelated T hh (s+R-1) (t+R-1) z0 w :=
    (positive_h_classical_label_regrade_heq _ _).trans
      (hhop.trans (positive_h_operation_heq T hh _ _ _ _
        (by simp only [hh,Nat.cast_one]) (by simp only [hh,Nat.cast_one]) z z0 hz0))
  have htarget : HEq
      (classicalLabelRegrade (X := T.Z)
        (q := (s+R-normalizedExponent background.classicalTower T.h+K,
          t+R-normalizedExponent background.classicalTower T.h+K-1))
        (by ext <;> dsimp <;> omega)
        (normalizedClassicalOperation T.Y T.Z T.g
          (s+R+normalizedExponent background.classicalTower T.f+K-1)
          (t+R+normalizedExponent background.classicalTower T.f+K-2) v))
      ((background.classical.map T.g).pageMap 2 (s+R+K-1,t+R+K-2) v0) :=
    (positive_h_classical_label_regrade_heq _ _).trans
      ((positive_h_normalized_operation_zero_heq T.Y T.Z T.g hg _ _ v).trans
        (positive_h_classical_map_label_heq T.Y T.Z T.g hvdeg v v0 hv0))
  have hdz0 := positive_h_classical_differential_heq T.Z K hzdeg
    (show (s+R-normalizedExponent background.classicalTower T.h+K,
      t+R-normalizedExponent background.classicalTower T.h+K-1)=(s+R+K-1,t+R+K-2) by
        simp only [hh,Nat.cast_one]
        ext <;> dsimp <;> omega)
    z z0 _ _ hz0 htarget hdz
  have hNC2' : ∀ a : Ambient background T.X (s+R+K-1,t+R+K-2),
      (background.classical.map T.f).pageMap 2 (s+R+K-1,t+R+K-2) a ∈
      boundaries background T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2) := by
    intro a
    exact positive_h_classical_boundary_heq T.Y ((R:ℤ)+K-2)
      (by simp only [hf,Nat.cast_zero,add_zero]) _ _
      (positive_h_normalized_operation_zero_heq T.X T.Y T.f hf _ _ a) (hNC2 a)
  obtain ⟨hy,hdy⟩ := positive_h_pdf_classical_corollary_RK T he hT hf hg hh
    R K hR hK s t x u z0 v0 w hu hw hdx hdz0 hNC1 hNC2'
  let y := normalizedClassicalOperation T.X T.Y T.f s t x
  let y0 := (background.classical.map T.f).pageMap 2 (s,t) x
  have hydeg : (s,t)=(s+normalizedExponent background.classicalTower T.f,
      t+normalizedExponent background.classicalTower T.f) := by simp only [hf,Nat.cast_zero,add_zero]
  have hyy : HEq y0 y := (positive_h_normalized_operation_zero_heq T.X T.Y T.f hf s t x).symm
  exact ⟨positive_h_classical_cycle_heq T.Y ((R:ℤ)+K-2) hydeg y0 y hyy hy,
    positive_h_classical_differential_heq T.Y ((R:ℤ)+K-1) hydeg hvdeg.symm
      y0 y v0 v hyy hv0.symm hdy⟩

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
