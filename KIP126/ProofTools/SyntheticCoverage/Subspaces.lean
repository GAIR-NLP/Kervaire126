module

public import KIP126.ProofTools.Language

import KIP126.SpectralSequence.FinitePageCalculus.Proofs
import KIP126.SpectralSequence.Computation.State.Proofs
import KIP126.AdamsSynthetic.Completed

/-! Candidate subspaces on the E₂ page for differential and permanence
criteria. The adapted-basis conditions (P.1)/(P.2) and no-unknown test (P.3)
give boundary completeness by cross-degree induction. The stopping-point
theorem preserves all permanent labels, including final boundaries.
Coordinate data and differential/permanence inputs are hypotheses. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))

private theorem represents_smul {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} {xr : E.Page r p}
    (h : RepresentsOnPage E r p x xr) (c : ℤ) :
    RepresentsOnPage E r p (c • x) (c • xr) := by
  obtain ⟨hr,z,hz,hzr⟩ := h
  exact ⟨hr,c • z,by rw [map_zsmul,hz],by rw [map_zsmul,hzr]⟩

/-- Early boundaries are E₂ labels representing zero on page r.
For `r=2`, the early boundary subgroup is zero. -/
@[no_expose] public def pageBoundaries (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    Submodule ℤ (E.Page 2 p) where
  carrier := {x | RepresentsOnPage E r p x 0}
  zero_mem' := RepresentsOnPage.zero hr
  add_mem' := by
    intro x y hx hy
    change RepresentsOnPage E r p (x+y) 0
    simpa only [add_zero] using middle_add hx hy
  smul_mem' := by
    intro c x hx
    have h := represents_smul E hx c
    rw [zsmul_zero] at h
    change RepresentsOnPage E r p _ 0
    convert h using 1
    exact int_smul_eq_zsmul _ c x

private theorem pageBoundaries_two (p : ℤ × ℤ) :
    pageBoundaries E 2 (by decide) p = ⊥ := by
  ext x
  change RepresentsOnPage E 2 p x 0 ↔ x = 0
  constructor
  · intro h
    exact h.eq_on_page_two
  · rintro rfl
    exact RepresentsOnPage.zero (by decide)

private theorem pageBoundaries_succ_iff (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (x : E.Page 2 p) :
    x ∈ pageBoundaries E (r+1) (by omega) p ↔ IsBoundaryBy E r p x := by
  constructor
  · intro h
    exact (h.eq_zero_iff_isBoundaryBy hr).mp rfl
  · rintro ⟨_,b,hb⟩
    let D := E.ssData p
    let m : WithTop ℕ := ↑(r+1-E.r₀).toNat
    refine ⟨by omega,Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) b,?_,?_⟩
    · change (Subobject.ofLE (D.B m) (D.Z m) _ ≫
        Subobject.ofLE (D.Z m) (D.Z ↑(2-E.r₀).toNat) _ ≫ D.pageπ _) b = x
      simpa only [D,m,←Category.assoc,Subobject.ofLE_comp_ofLE] using hb
    · exact cokernel.condition_apply _ b

private theorem permanent_reaches {p : ℤ × ℤ} {x : E.Page 2 p}
    (hx : IsPermanentCycle E p x) (r : ℤ) (hr : 2 ≤ r) :
    ReachesPage E r p x := by
  obtain ⟨z,hz⟩ := hx
  let D := E.ssData p
  let m : WithTop ℕ := ↑(r-E.r₀).toNat
  let zr := Subobject.ofLE (D.Z ⊤) (D.Z m) (D.Z_anti le_top) z
  refine ⟨D.pageπ m zr,hr,zr,?_,rfl⟩
  dsimp only [zr]
  rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

/-- A boundary after page r has an incoming page-r representative
under the spectral sequence’s boundary and differential operations. -/
private theorem boundary_next_has_differential
    (hstart : E.r₀ ≤ 2) (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    {y : E.Page 2 (p+E.diffDeg r)}
    (hy : y ∈ pageBoundaries E (r+1) (by omega) (p+E.diffDeg r)) :
    ∃ x : E.Page 2 p, HasDifferential E r p (p+E.diffDeg r) x y := by
  obtain ⟨_,z,hz2,hznext⟩ := hy
  have hn : (r+1-E.r₀).toNat = (r-E.r₀).toNat+1 := by omega
  let A := E.ssData (p+E.diffDeg r)
  let n := (r-E.r₀).toNat
  let z' : (Subobject.underlying.obj (A.Z ↑(n+1)) : ModuleCat ℤ) :=
    Subobject.ofLE (A.Z ↑(r+1-E.r₀).toNat) (A.Z ↑(n+1)) (by
      dsimp only [n]; rw [hn]) z
  have transport_zero (D : SSData (ModuleCat.{v} ℤ)) (a b : WithTop ℕ)
      (hab : a = b) (w : (Subobject.underlying.obj (D.Z a) : ModuleCat ℤ))
      (hw : D.pageπ a w = 0) :
      D.pageπ b (Subobject.ofLE (D.Z a) (D.Z b) (by rw [hab]) w) = 0 := by
    subst b
    simpa using hw
  have hz' : A.pageπ ↑(n+1) z' = 0 :=
    transport_zero A _ _ (by dsimp only [n]; exact_mod_cast hn) z hznext
  have hin := (next_projection_zero_iff_incoming E r (hstart.trans hr) p z').mp hz'
  obtain ⟨xr,hxr⟩ := hin
  obtain ⟨x,hx⟩ := page_has_initial_representative hr xr
  let yr := (Subobject.ofLE _ _ (A.Z_anti
    (by exact_mod_cast Nat.le_succ n)) ≫ A.pageπ ↑n) z'
  have hyrep : RepresentsOnPage E r (p+E.diffDeg r) y yr := by
    refine ⟨hr,Subobject.ofLE _ _ (A.Z_anti
      (by exact_mod_cast Nat.le_succ n)) z',?_,rfl⟩
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    dsimp only [z']
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  exact ⟨x,rfl,xr,yr,hx,hyrep,by simpa only [eqToHom_refl,Category.comp_id] using hxr⟩

/-- Finite adapted blocks from (P.1) with differential equations
and whole-block injectivity (P.2). The index q denotes page q+2.
The base is the sum of supplied boundaries and permanent cycles;
coordinate projections may be obtained from any adapted basis. -/
private structure AdaptedBlocks where
  known : ∀ (_n : ℕ) (p : ℤ × ℤ), Submodule ℤ (E.Page 2 p)
  known_valid : ∀ n p, known n p ≤ pageBoundaries E ((n:ℤ)+2) (by omega) p
  known_mono : ∀ p, Monotone (fun n => known n p)
  size : ℤ × ℤ → ℕ
  base : ∀ p, E.Page 2 p → E.Page 2 p
  k : ∀ (_q : ℕ) (p : ℤ × ℤ), E.Page 2 p → E.Page 2 p
  t : ∀ (_q : ℕ) (p : ℤ × ℤ), E.Page 2 p → E.Page 2 p
  value : ∀ (q : ℕ) (p : ℤ × ℤ), E.Page 2 p → E.Page 2 (p+E.diffDeg ((q:ℤ)+2))
  base_permanent : ∀ p x, IsPermanentCycle E p (base p x)
  k_reaches : ∀ (q : ℕ) p x, ReachesPage E ((q:ℤ)+2) p (k q p x)
  t_reaches : ∀ (q : ℕ) p x, ReachesPage E ((q:ℤ)+2) p (t q p x)
  outside : ∀ q p x, size p ≤ q → k q p x = 0 ∧ t q p x = 0
  decomposition : ∀ p x, x = base p x +
    ∑ q ∈ Finset.range (size p), (k q p x+t q p x)
  differential : ∀ (q : ℕ) p x,
    HasDifferential E ((q:ℤ)+2) p (p+E.diffDeg ((q:ℤ)+2)) (k q p x) (value q p x)
  value_known : ∀ q p x, value q p x ∈ known (q+1) (p+E.diffDeg ((q:ℤ)+2))
  injective_mod_known : ∀ q p x,
    value q p x ∈ known q (p+E.diffDeg ((q:ℤ)+2)) → k q p x = 0

/-- Exactly (P.3): at each possible incoming source no unresolved block has
page at most the page of that incoming differential. -/
private def AdaptedBlocks.NoUnknown (A : AdaptedBlocks E) (p : ℤ × ℤ) (N : ℕ) : Prop :=
  ∀ r < N, ∀ q ≤ r, ∀ x, A.t q (p-E.diffDeg ((r:ℤ)+2)) x = 0

private theorem reaches_add {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p}
    (hx : ReachesPage E r p x) (hy : ReachesPage E r p y) :
    ReachesPage E r p (x+y) := by
  obtain ⟨xr,hxr⟩ := hx
  obtain ⟨yr,hyr⟩ := hy
  exact ⟨xr+yr,middle_add hxr hyr⟩

private theorem reaches_sum {ι : Type*} (s : Finset ι) {r : ℤ} (hr : 2 ≤ r)
    {p : ℤ × ℤ} (f : ι → E.Page 2 p)
    (hf : ∀ i ∈ s, ReachesPage E r p (f i)) :
    ReachesPage E r p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show ReachesPage E r p 0 from ⟨0,RepresentsOnPage.zero hr⟩)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact reaches_add E (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- After all earlier known blocks have vanished and all unresolved blocks
through the required page are absent, every term other than block q survives
past page q+2. This uses the finite decomposition itself. -/
private theorem AdaptedBlocks.remainder_reaches
    (A : AdaptedBlocks E) (p : ℤ × ℤ) (q R : ℕ) (hq : q ≤ R)
    (x : E.Page 2 p)
    (hearly : ∀ j < q, A.k j p x = 0)
    (hunknown : ∀ j ≤ R, A.t j p x = 0) :
    ReachesPage E ((q:ℤ)+3) p (x-A.k q p x) := by
  classical
  let S := Finset.range (A.size p)
  let rem := A.base p x + (∑ j ∈ S.erase q, A.k j p x) +
    ∑ j ∈ S, A.t j p x
  have hsum : (∑ j ∈ S, A.k j p x) = A.k q p x + ∑ j ∈ S.erase q, A.k j p x := by
    by_cases hmem : q ∈ S
    · exact (Finset.add_sum_erase S (fun j => A.k j p x) hmem).symm
    · have hqN : A.size p ≤ q := by simpa only [S,Finset.mem_range,not_lt] using hmem
      rw [(A.outside q p x hqN).1,zero_add,Finset.erase_eq_of_notMem hmem]
  have hrem : x-A.k q p x = rem := by
    conv_lhs => lhs; rw [A.decomposition p x]
    rw [Finset.sum_add_distrib]
    change (A.base p x + ((∑ j ∈ S, A.k j p x)+∑ j ∈ S,A.t j p x)) - A.k q p x = rem
    rw [hsum]
    dsimp only [rem]
    abel
  rw [hrem]
  apply reaches_add E
  · apply reaches_add E (permanent_reaches E (A.base_permanent p x) _ (by omega))
    apply reaches_sum E _ (by omega)
    intro j hj
    have hjq : j ≠ q := (Finset.mem_erase.mp hj).1
    by_cases hjlt : j < q
    · rw [hearly j hjlt]
      exact ⟨0,RepresentsOnPage.zero (by omega)⟩
    · exact reaches_earlier (by omega) (by omega : (q:ℤ)+3 ≤ (j:ℤ)+2) (A.k_reaches j p x)
  · apply reaches_sum E _ (by omega)
    intro j _
    by_cases hjR : j ≤ R
    · rw [hunknown j hjR]
      exact ⟨0,RepresentsOnPage.zero (by omega)⟩
    · exact reaches_earlier (by omega) (by omega : (q:ℤ)+3 ≤ (j:ℤ)+2) (A.t_reaches j p x)

private theorem differential_target_boundary_of_source_later
    (hstart : E.r₀ ≤ 2) (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    {x : E.Page 2 p} {y : E.Page 2 (p+E.diffDeg r)}
    (hd : HasDifferential E r p (p+E.diffDeg r) x y)
    (hx : ReachesPage E (r+1) p x) :
    y ∈ pageBoundaries E r hr (p+E.diffDeg r) := by
  obtain ⟨_,xr,yr,hxr,hyr,hdxy⟩ := hd
  have hx0 := represents_d_zero_of_later (hstart.trans hr)
    (by omega : r < r+1) hxr hx
  have hy0 : yr = 0 := by simpa only [eqToHom_refl,Category.comp_id,hx0] using hdxy.symm
  change RepresentsOnPage E r _ y 0
  simpa only [hy0] using hyr

private theorem reaches_sub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p}
    (hx : ReachesPage E r p x) (hy : ReachesPage E r p y) :
    ReachesPage E r p (x-y) := by
  obtain ⟨xr,hxr⟩ := hx
  obtain ⟨yr,hyr⟩ := hy
  exact ⟨xr-yr,represents_sub hxr hyr⟩

private theorem boundary_complete_of_targets
    (hstart : E.r₀ ≤ 2) (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (known : Submodule ℤ (E.Page 2 (p+E.diffDeg r)))
    (hearlier : pageBoundaries E r hr (p+E.diffDeg r) ≤ known)
    (hvalid : known ≤ pageBoundaries E (r+1) (by omega) (p+E.diffDeg r))
    (htarget : ∀ x, ReachesPage E r p x → ∃ y ∈ known,
      HasDifferential E r p (p+E.diffDeg r) x y) :
    pageBoundaries E (r+1) (by omega) (p+E.diffDeg r) = known := by
  apply le_antisymm _ hvalid
  intro y hy
  obtain ⟨x,_,xr,yr,hxr,hyr,hxy⟩ := boundary_next_has_differential E hstart r hr p hy
  obtain ⟨z,hz,_,xr',zr,hxr',hzr,hxz⟩ := htarget x ⟨xr,hxr⟩
  have hxx := hxr.unique hxr'
  have hyz : yr = zr := by
    have ha : E.d r p xr = yr := by simpa using hxy
    have hb : E.d r p xr' = zr := by simpa using hxz
    exact ha.symm.trans ((congrArg (E.d r p) hxx).trans hb)
  have hdiff : y-z ∈ pageBoundaries E r hr (p+E.diffDeg r) := by
    change RepresentsOnPage E r _ (y-z) 0
    simpa only [hyz,sub_self] using represents_sub hyr hzr
  simpa only [sub_add_cancel] using known.add_mem (hearlier hdiff) hz

/-- Boundary completeness: the no-unknown condition (P.3), the
finite adapted decomposition (P.1), and whole-block injectivity (P.2)
force all actual early boundaries to be the supplied boundaries.
The proof is simultaneous in every bidegree; the Adams differential degree
is needed in the intermediate-degree reindexing. -/
private theorem AdaptedBlocks.boundary_complete
    (A : AdaptedBlocks E) (hstart : E.r₀ ≤ 2)
    (hdeg : ∀ n : ℕ, E.diffDeg ((n:ℤ)+2) = ((n:ℤ)+2,(n:ℤ)+1)) :
    ∀ N p, A.NoUnknown E p N →
      pageBoundaries E ((N:ℤ)+2) (by omega) p = A.known N p := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero =>
      intro p _
      apply le_antisymm
      · change pageBoundaries E 2 (by decide) p ≤ A.known 0 p
        rw [pageBoundaries_two]
        exact bot_le
      · exact A.known_valid 0 p
    | succ R =>
      intro d hno
      let p := d-E.diffDeg ((R:ℤ)+2)
      have hp : p+E.diffDeg ((R:ℤ)+2) = d := sub_add_cancel _ _
      have hunknown : ∀ j ≤ R, ∀ x, A.t j p x = 0 :=
        fun j hj x => hno R (by omega) j hj x
      have hprev : pageBoundaries E ((R:ℤ)+2) (by omega) d = A.known R d :=
        ih R (by omega) d (fun r hr q hq x => hno r (by omega) q hq x)
      have htargets : ∀ x, ReachesPage E ((R:ℤ)+2) p x →
          ∃ y ∈ A.known (R+1) (p+E.diffDeg ((R:ℤ)+2)),
            HasDifferential E ((R:ℤ)+2) p (p+E.diffDeg ((R:ℤ)+2)) x y := by
        intro x hx
        have hearly : ∀ q < R, A.k q p x = 0 := by
          intro q
          induction q using Nat.strong_induction_on with
          | h q iq =>
            intro hq
            have hlocal : A.NoUnknown E (p+E.diffDeg ((q:ℤ)+2)) q := by
              intro j hj k hk
              have heq : p+E.diffDeg ((q:ℤ)+2)-E.diffDeg ((j:ℤ)+2) =
                  d-E.diffDeg (((R-q+j:ℕ):ℤ)+2) := by
                dsimp only [p]
                rw [hdeg,hdeg,hdeg,hdeg]
                ext <;> simp only [Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add] <;> omega
              rw [heq]
              intro z
              exact hno (R-q+j) (by omega) k (by omega) z
            have hcomplete := ih q (by omega) (p+E.diffDeg ((q:ℤ)+2)) hlocal
            have hrem := A.remainder_reaches E p q R (by omega) x
              (fun j hj => iq j hj (by omega)) (fun j hj => hunknown j hj x)
            have hx' : ReachesPage E ((q:ℤ)+3) p x :=
              reaches_earlier (by omega) (by omega) hx
            have hk : ReachesPage E (((q:ℤ)+2)+1) p (A.k q p x) := by
              have hh := reaches_sub E hx' hrem
              have he : x-(x-A.k q p x) = A.k q p x := by abel
              simpa only [he,show (q:ℤ)+2+1 = (q:ℤ)+3 by omega] using hh
            have hb := differential_target_boundary_of_source_later E hstart
              ((q:ℤ)+2) (by omega) p (A.differential q p x) hk
            exact A.injective_mod_known q p x (hcomplete ▸ hb)
        have hrem := A.remainder_reaches E p R R le_rfl x hearly
          (fun j hj => hunknown j hj x)
        obtain ⟨_,kr,yr,hkr,hyr,hdk⟩ := A.differential R p x
        obtain ⟨xr,hxr⟩ := hx
        obtain ⟨zr,hzr⟩ := reaches_earlier (by omega : (2:ℤ) ≤ (R:ℤ)+2)
          (by omega : (R:ℤ)+2 ≤ (R:ℤ)+3) hrem
        have hsum : RepresentsOnPage E ((R:ℤ)+2) p x (kr+zr) := by
          have hh := middle_add hkr hzr
          have he : A.k R p x+(x-A.k R p x) = x := by abel
          simpa only [he] using hh
        have hz0 := represents_d_zero_of_later (by omega : E.r₀ ≤ (R:ℤ)+2)
          (by omega : (R:ℤ)+2 < (R:ℤ)+3) hzr hrem
        refine ⟨A.value R p x,A.value_known R p x,rfl,xr,yr,hxr,hyr,?_⟩
        have hsame := hxr.unique hsum
        simpa only [eqToHom_refl,Category.comp_id,hsame,map_add,hz0,add_zero] using hdk
      have hresult := boundary_complete_of_targets E hstart ((R:ℤ)+2) (by omega) p
        (A.known (R+1) (p+E.diffDeg ((R:ℤ)+2)))
        (by rw [hp,hprev]; exact A.known_mono d (by omega))
        (by simpa only [Nat.cast_add,Nat.cast_one,show (R:ℤ)+1+2 = (R:ℤ)+2+1 by omega]
          using A.known_valid (R+1) (p+E.diffDeg ((R:ℤ)+2))) htargets
      have hresultd : pageBoundaries E ((R:ℤ)+2+1) (by omega) d = A.known (R+1) d :=
        Eq.mp (congrArg (fun a => pageBoundaries E ((R:ℤ)+2+1) (by omega) a =
          A.known (R+1) a) hp) hresult
      simpa only [Nat.cast_add,Nat.cast_one,show (R:ℤ)+1+2 = (R:ℤ)+2+1 by omega] using hresultd

/-- The span after stopping before block L: retain the boundary/permanent
base and every known or unresolved block whose page is at least L+2. -/
private def AdaptedBlocks.retainedSubspace (A : AdaptedBlocks E)
    (p : ℤ × ℤ) (L : ℕ) : Submodule ℤ (E.Page 2 p) :=
  Submodule.span ℤ {x |
    (∃ v, A.base p v = x) ∨
    (∃ q, L ≤ q ∧ ∃ v, A.k q p v = x) ∨
    (∃ q, L ≤ q ∧ ∃ v, A.t q p v = x)}

/-- Permanent-label retention under block deletion before the stopping
point. Deletion requires no unresolved direction and condition (P.3)
at the target, except for an already-zero block. The boundary argument
gives boundary completeness. Permanent labels with zero E∞ class are included. -/
private theorem AdaptedBlocks.permanent_retention
    (A : AdaptedBlocks E) (hstart : E.r₀ ≤ 2)
    (hdeg : ∀ n : ℕ, E.diffDeg ((n:ℤ)+2) = ((n:ℤ)+2,(n:ℤ)+1))
    (p : ℤ × ℤ) (L : ℕ)
    (hunknown : ∀ q < L, ∀ x, A.t q p x = 0)
    (htest : ∀ q < L, (∀ x, A.k q p x = 0) ∨
      A.NoUnknown E (p+E.diffDeg ((q:ℤ)+2)) q) :
    ∀ x, IsPermanentCycle E p x → x ∈ A.retainedSubspace E p L := by
  intro x hx
  have hearly : ∀ q < L, A.k q p x = 0 := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hq
      rcases htest q hq with hzero | hno
      · exact hzero x
      · have hcomplete := A.boundary_complete E hstart hdeg q _ hno
        have hrem := A.remainder_reaches E p q q le_rfl x
          (fun j hj => ih j hj (by omega)) (fun j hj => hunknown j (by omega) x)
        have hk : ReachesPage E (((q:ℤ)+2)+1) p (A.k q p x) := by
          have hh := reaches_sub E (permanent_reaches E hx ((q:ℤ)+3) (by omega)) hrem
          have he : x-(x-A.k q p x) = A.k q p x := by abel
          simpa only [he,show (q:ℤ)+2+1 = (q:ℤ)+3 by omega] using hh
        have hb := differential_target_boundary_of_source_later E hstart
          ((q:ℤ)+2) (by omega) p (A.differential q p x) hk
        exact A.injective_mod_known q p x (hcomplete ▸ hb)
  rw [A.decomposition p x]
  apply Submodule.add_mem
  · exact Submodule.subset_span (Or.inl ⟨x,rfl⟩)
  · apply Submodule.sum_mem
    intro q _
    apply Submodule.add_mem
    · by_cases hq : q < L
      · rw [hearly q hq]; exact Submodule.zero_mem _
      · exact Submodule.subset_span (Or.inr (Or.inl ⟨q,by omega,x,rfl⟩))
    · by_cases hq : q < L
      · rw [hunknown q hq x]; exact Submodule.zero_mem _
      · exact Submodule.subset_span (Or.inr (Or.inr ⟨q,by omega,x,rfl⟩))

/-- The complete boundary theorem applied to the repository's fixed Adams
sequence, with its actual initial page and differential bidegree. The adapted
basis data remain mathematical premises, not values read from a database. -/
private theorem standard_boundary_complete
    (X : KIP126.AdamsSynthetic.Completed.Spectrum)
    (A : AdaptedBlocks (KIP126.AdamsSynthetic.Completed.classical.obj X))
    (N : ℕ) (p : ℤ × ℤ)
    (hno : A.NoUnknown (KIP126.AdamsSynthetic.Completed.classical.obj X) p N) :
    pageBoundaries (KIP126.AdamsSynthetic.Completed.classical.obj X)
      ((N:ℤ)+2) (by omega) p = A.known N p := by
  apply A.boundary_complete _ _ _ N p hno
  · rw [KIP126.AdamsSynthetic.Completed.classical.firstPage]
  · intro n
    rw [KIP126.AdamsSynthetic.Completed.classical.differentialDegree]
    congr 1
    omega

private theorem standard_permanent_retention
    (X : KIP126.AdamsSynthetic.Completed.Spectrum)
    (A : AdaptedBlocks (KIP126.AdamsSynthetic.Completed.classical.obj X))
    (p : ℤ × ℤ) (L : ℕ)
    (hunknown : ∀ q < L, ∀ x, A.t q p x = 0)
    (htest : ∀ q < L, (∀ x, A.k q p x = 0) ∨
      A.NoUnknown (KIP126.AdamsSynthetic.Completed.classical.obj X)
        (p+(KIP126.AdamsSynthetic.Completed.classical.obj X).diffDeg ((q:ℤ)+2)) q) :
    ∀ x, IsPermanentCycle (KIP126.AdamsSynthetic.Completed.classical.obj X) p x →
      x ∈ A.retainedSubspace (KIP126.AdamsSynthetic.Completed.classical.obj X) p L := by
  apply A.permanent_retention _ _ _ p L hunknown htest
  · rw [KIP126.AdamsSynthetic.Completed.classical.firstPage]
  · intro n
    rw [KIP126.AdamsSynthetic.Completed.classical.differentialDegree]
    congr 1
    omega

end
end KIP126.ProofTools.Internal.SyntheticCoverage
