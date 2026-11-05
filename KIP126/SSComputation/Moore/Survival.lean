module

public import KIP126.SSComputation.Moore.Data
import KIP126.SSComputation.Table
import KIP126.SpectralSequence.FinitePageCalculus.Proofs
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
import KIP126.AdamsComputation.E2
import KIP126.ProofTools.Representatives

/-! Finite-page consequences of the Moore route's two ordinary SS inputs.
The consequences use the two inputs from `Moore.Data`; the two d₃
inputs killing the sphere E₈ target belong to the fixed SS table. -/

@[expose] section
namespace KIP126.SSComputation.Moore
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Computation.Table
open KIP126.AdamsSynthetic.Completed (background)
noncomputable section
universe v
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem cycle_successor_lift
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ↑(r-E.r₀).toNat) : ModuleCat.{v} ℤ))
    (hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z) = 0) :
    ∃ zn : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ),
      (Subobject.ofLE _ _ ((E.ssData p).Z_anti (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat))) zn = z := by
  classical
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hsucc : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hsucc)
  have hker : D.pageπ ↑n z ∈ LinearMap.ker (E.d r p).hom := hz
  rw [←subobjectModule_kernel,E.Z_succ r p hr,subobjectModule_image] at hker
  obtain ⟨z',hz'⟩ := hker
  change D.pageπ ↑n (i z') = D.pageπ ↑n z at hz'
  have hzero : D.pageπ ↑n (z-i z')=0 := by rw [map_sub,hz',sub_self]
  have hb : ∃ b : (Subobject.underlying.obj (D.B ↑n) : ModuleCat.{v} ℤ),
      (Subobject.ofLE (D.B ↑n) (D.Z ↑n) (D.B_le_Z _)) b = z-i z' :=
    (cokernel_π_eq_zero_iff_mem_range _ _).mp hzero
  obtain ⟨b,hb⟩ := hb
  have hBZ : D.B ↑n ≤ D.Z ↑(n+1) := (D.B_mono hsucc).trans (D.B_le_Z _)
  let zn : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{v} ℤ) :=
    z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ) b
  have hnz : i zn=z := by
    dsimp only [zn]
    rw [map_add]
    change i z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ ≫ i) b = z
    dsimp only [i]
    rw [Subobject.ofLE_comp_ofLE,hb]
    abel
  exact ⟨zn,hnz⟩


private theorem reaches_next_of_zero
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r) {p : ℤ × ℤ}
    {x : E.Page 2 p} {a : E.Page r p}
    (ha : RepresentsOnPage E r p x a) (hzero : E.d r p a=0) :
    ReachesPage E (r+1) p x := by
  obtain ⟨_,z,hz2,hza⟩ := ha
  have hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z)=0 := by
    rw [hza]
    exact hzero
  obtain ⟨zn,hnz⟩ := cycle_successor_lift E r hr0 p z hz
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let m : WithTop ℕ := ↑(r+1-E.r₀).toNat
  have he : (↑((r-E.r₀).toNat+1) : WithTop ℕ)=m := by
    dsimp only [m]
    congr 1
    omega
  have hnm : n≤m := by dsimp only [n,m]; exact_mod_cast (show (r-E.r₀).toNat≤(r+1-E.r₀).toNat by omega)
  have cast_lift (m' : WithTop ℕ) (h : m'=m)
      (v : (Subobject.underlying.obj (A.Z m') : ModuleCat ℤ))
      (hn : n≤m')
      (hv : Subobject.ofLE (A.Z m') (A.Z n) (A.Z_anti hn) v=z) :
      ∃ w : (Subobject.underlying.obj (A.Z m) : ModuleCat ℤ),
        Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) w=z := by
    subst m'
    exact ⟨v,hv⟩
  obtain ⟨w,hw⟩ := cast_lift _ he zn
    (by dsimp only [n]; exact_mod_cast Nat.le_succ (r-E.r₀).toNat) hnz
  refine ⟨A.pageπ m w,by omega,w,?_,rfl⟩
  calc
    (Subobject.ofLE (A.Z m) (A.Z _) _ ≫ A.pageπ _) w =
      (Subobject.ofLE (A.Z n) (A.Z ↑(2-E.r₀).toNat)
        (A.Z_anti (by dsimp only [n]; exact_mod_cast
          (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega))) ≫ A.pageπ _)
        ((Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)) w) := by
          rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    _ = x := by rw [hw]; exact hz2

private theorem target_d3_0 :
    HasDifferential background.classical.sphere 3 (14,137) (17,139)
      (basis .sphere 14 137 0) (basis .sphere 17 139 0) := by
  have h := result ⟨.sphere, .equation, 3, 14, 137, [0], 17, 139, [0]⟩ (List.mem_of_getElem? (i := 113) rfl)
  obtain ⟨x,hx,y,hy,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [0]=true := rfl
  delta decode at hx hy
  simp only [vx,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at hx
  simp only [vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at hy
  rw [←hx,←hy] at hd
  exact hd

private theorem target_d3_1 :
    HasDifferential background.classical.sphere 3 (14,137) (17,139)
      (basis .sphere 14 137 1) (basis .sphere 17 139 1) := by
  have h := result ⟨.sphere, .equation, 3, 14, 137, [1], 17, 139, [1]⟩ (List.mem_of_getElem? (i := 112) rfl)
  obtain ⟨x,hx,y,hy,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [1]=true := rfl
  delta decode at hx hy
  simp only [vx,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at hx
  simp only [vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at hy
  rw [←hx,←hy] at hd
  exact hd

private theorem target_page_eight_zero :
    Subsingleton (background.classical.sphere.Page 8 (17,139)) := by
  classical
  let E := background.classical.sphere
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,17,139,["13,3,76,1", "0,1,437,1"]⟩
    (List.mem_of_getElem? (i := 237) rfl)
  change E.Page 2 (17,139) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=basis .sphere 17 139 i.val at he
  have h0 : RepresentsOnPage E 8 (17,139) (e.symm (Finsupp.single 0 1)) 0 := by
    rw [he]
    exact differential_target_later_zero
      (by change background.classical.sphere.r₀≤3; rw [background.classical.firstPage]; decide)
      (by decide) target_d3_0
  have h1 : RepresentsOnPage E 8 (17,139) (e.symm (Finsupp.single 1 1)) 0 := by
    rw [he]
    exact differential_target_later_zero
      (by change background.classical.sphere.r₀≤3; rw [background.classical.firstPage]; decide)
      (by decide) target_d3_1
  have hall (x : E.Page 8 (17,139)) : x=0 := by
    rcases generated_two (by decide) e 0 0 h0 h1 x with h|h|h|h
    all_goals simpa using h
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

private theorem reaches_next_of_zero_differential
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r : ℤ} {p q : ℤ×ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀≤r) (hr : 2≤r) (hd : HasDifferential E r p q x 0) :
    ReachesPage E (r+1) p x := by
  obtain ⟨rfl,a,b,ha,hb,hab⟩ := hd
  have hb0 : b=0 := represents_unique hb (RepresentsOnPage.zero hr)
  have hd0 : E.d r p a=0 := by
    simpa only [eqToHom_refl,Category.comp_id,hb0] using hab
  exact reaches_next_of_zero hr0 hr ha hd0

private theorem v_reaches_nine_of_d7_zero
    (hd : HasDifferential background.classical.sphere 7 (9,132) (16,138)
      KIP126.Computation.Standard.V 0) :
    ReachesPage background.classical.sphere 9 (9,132) KIP126.Computation.Standard.V := by
  have h8 : ReachesPage background.classical.sphere 8 (9,132) KIP126.Computation.Standard.V :=
    reaches_next_of_zero_differential
      (E := background.classical.sphere) (r := 7) (p := (9,132)) (q := (16,138))
      (by rw [background.classical.firstPage]; decide) (by decide) hd
  obtain ⟨a8,ha8⟩ := h8
  haveI : Subsingleton (background.classical.sphere.Page 8
      ((9,132)+background.classical.sphere.diffDeg 8)) := by
    simpa only [background.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,
      Int.reduceSub] using target_page_eight_zero
  exact reaches_next_of_zero
    (E := background.classical.sphere) (r := 8) (p := (9,132))
    (by rw [background.classical.firstPage]; decide) (by decide) ha8 (Subsingleton.elim _ _)

/-- The zero d₄ equation implies the fourth-cycle condition used by the Moore lift. -/
private theorem bottom_source_cycles_four_of_d4_zero
    (hd : HasDifferential KIP126.AdamsComputation.Moore.sequence 4 (8,132) (12,135)
      KIP126.AdamsComputation.Moore.bottomSource 0) :
    KIP126.AdamsComputation.Moore.bottomSource ∈
      KIP126.Literature.cycles background KIP126.AdamsComputation.Moore.adamsObject
        4 (8,132) := by
  have h5 := reaches_next_of_zero_differential
    (E := KIP126.AdamsComputation.Moore.sequence) (r := 4) (p := (8,132)) (q := (12,135))
    (by rw [background.classical.firstPage]; decide) (by decide) hd
  exact ((KIP126.ProofTools.isCycle_iff_reaches background
    KIP126.AdamsComputation.Moore.adamsObject 5 (by decide) (8,132)
    KIP126.AdamsComputation.Moore.bottomSource).mpr h5).2

/-- The zero third differential follows from the fourth-page input. -/
private theorem bottom_source_d3_zero_of_d4_zero
    (hd : HasDifferential KIP126.AdamsComputation.Moore.sequence 4 (8,132) (12,135)
      KIP126.AdamsComputation.Moore.bottomSource 0) :
    HasDifferential KIP126.AdamsComputation.Moore.sequence 3 (8,132) (11,134)
      KIP126.AdamsComputation.Moore.bottomSource 0 := by
  obtain ⟨_,a4,_,ha4,_,_⟩ := hd
  obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha4
  have hz := represents_d_zero_of_later
    (by rw [background.classical.firstPage]; decide) (by decide : (3:ℤ)<4) ha3 ⟨a4,ha4⟩
  have hdeg : (8,132)+KIP126.AdamsComputation.Moore.sequence.diffDeg 3=(11,134) := by
    simp only [KIP126.AdamsComputation.Moore.sequence,background.classical.differentialDegree,
      Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  refine ⟨hdeg,a3,0,ha3,RepresentsOnPage.zero (by decide),?_⟩
  rw [CategoryTheory.comp_apply,hz,map_zero]

/-- The zero d₃ follows from the fixed d₄ input. -/
public theorem bottom_source_d3_zero :
    HasDifferential KIP126.AdamsComputation.Moore.sequence 3 (8,132) (11,134)
      KIP126.AdamsComputation.Moore.bottomSource 0 :=
  bottom_source_d3_zero_of_d4_zero bottom_source_d4_zero

/-- The actual Moore bottom-cell source is a fourth cycle, using
`bottom_source_d4_zero`. -/
public theorem bottom_source_cycles_four :
    KIP126.AdamsComputation.Moore.bottomSource ∈
      KIP126.Literature.cycles background KIP126.AdamsComputation.Moore.adamsObject
        4 (8,132) :=
  bottom_source_cycles_four_of_d4_zero bottom_source_d4_zero

/-- V reaches E₉: the d₇ equation gives an E₈ representative, and the two
d₃ equations kill the possible d₈ target. -/
public theorem v_cycles_eight :
    KIP126.Computation.Standard.V ∈
      KIP126.Literature.cycles background .sphere 8 (9,132) := by
  exact ((KIP126.ProofTools.isCycle_iff_reaches background .sphere 9 (by decide)
    (9,132) KIP126.Computation.Standard.V).mpr
      (v_reaches_nine_of_d7_zero v_d7_zero)).2

end
end KIP126.SSComputation.Moore
end
