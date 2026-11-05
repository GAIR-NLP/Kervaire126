module
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.ExtensionImage
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
import KIP126.AdamsComputation.Table.Dimensions
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingRange

/-! Boundary perturbations and exact-source obstructions for Mahowald extensions.
Write `k=l-e(h)`. Adding `B_(k+1)` to the h-target at lambda layer k
preserves its E∞ label with the same finite witness. A positive-length
f-extension of an exact source forces its normalized leading E₂ image to vanish.

The rotated nu triangle `S^0 -> Cnu -> S^4 -> S^1`, with
`(ef,eg,eh)=(0,0,1)`, `(n,m,l,s,t)=(1,0,2,1,16)`,
`x=d₂(h₄)=h₀*h₃²` in `Ext^(3,17)`, and `xBar=y=yBar=0`
is a counterexample. Here `i=2,q=1,k=1,Q=2`; normalized rotation,
the extension premises, and nonvanishing of the bottom leading image hold.

Wu, arXiv:2606.02779v2, Theorem 4.23 gives a `(j+l)`-layer extension.
Remark 4.25 requires `f(x)=0` on E₂ and boundary conditions to lower
the layer. Remarks 3.3–3.4 allow inessential input extensions. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.Core.SpectralSequence.FinitePageCalculus
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem cycle_add_boundary (X : AdamsObject (coefficients := background.coefficients)) (r k : ℤ)
    (p : ℤ × ℤ) (x b : Ambient background X p)
    (hx : IsCycle background X r p x) (hb : b∈boundaries background X k p) :
    IsCycle background X r p (x+b) := by
  exact ⟨hx.1,(cycles background X r p).add_mem hx.2 (boundaries_le_cycles background X p k r hb)⟩

private theorem finite_target_rep_add_boundary (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hkq : k<q) (s t : ℤ) (x b : Ambient background X (s,t))
    (hb : b∈boundaries background X (k+1) (s,t))
    (e : ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData
      (s,t,t-k)).eInfty)
    (hx : HasInfinityRepresentative _ 2 (s,t,t-k) (finiteTargetLabel background X q s t k x) e) :
    HasInfinityRepresentative _ 2 (s,t,t-k) (finiteTargetLabel background X q s t k (x+b)) e := by
  have hlabel (z : Ambient background X (s,t)) : nuWeightLabel background X s t (t-k) (by omega) z =
      targetNuLabel background X s t k z := by
    have hk' : (t-(t-k)).toNat=k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel background X s t a z) = targetNuLabel background X s t b z := by
      subst b; rfl
    exact transport _ k hk' _
  have hrep := KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
    s t (t-k) (by omega) x e
  rw [hlabel] at hrep
  obtain ⟨hxc,hxe⟩ := hrep.mp hx
  have hbc : b∈cycles background X (q-t+(t-k)) (s,t) :=
    boundaries_le_cycles background X (s,t) (k+1) _ hb
  have hxbc := (cycles background X (q-t+(t-k)) (s,t)).add_mem hxc hbc
  have hb' : b∈boundaries background X (1+t-(t-k)) (s,t) := by
    convert hb using 1; congr 1; omega
  have hbzero : subquotientClass (cycles background X (q-t+(t-k)) (s,t))
      (boundaries background X (1+t-(t-k)) (s,t)) ⟨b,hbc⟩=0 :=
    (CrossingLabels.subquotient_zero_iff _ _ _).mpr hb'
  have hclass : subquotientClass (cycles background X (q-t+(t-k)) (s,t))
      (boundaries background X (1+t-(t-k)) (s,t)) ⟨x+b,hxbc⟩=
      subquotientClass (cycles background X (q-t+(t-k)) (s,t))
        (boundaries background X (1+t-(t-k)) (s,t)) ⟨x,hxc⟩ := by
    change subquotientClass _ _ (⟨x,hxc⟩+⟨b,hbc⟩)=_
    rw [map_add,hbzero,add_zero]
  have hrep' := KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
    s t (t-k) (by omega) (x+b) e
  rw [hlabel] at hrep'
  exact hrep'.mpr ⟨hxbc,hxe.trans hclass.symm⟩

private def finite_extension_target_add_boundary (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (n s t : ℤ) (x : Ambient background X (s,t))
    (y b : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f r n s t x y)
    (hb : b∈boundaries background Y (1+n-normalizedExponent background.classicalTower f) (s+n,t+n)) :
    FiniteExtensionWitness background X Y f r n s t x (y+b) := by
  let k : ℕ := (n-normalizedExponent background.classicalTower f).toNat
  have hk : (k:ℤ)=n-normalizedExponent background.classicalTower f :=
    Int.toNat_of_nonneg (by have := W.length_lower; omega)
  have hkq : k<r-1 := by have := W.length_upper; have := W.page_ge_two; omega
  have hb' : b∈boundaries background Y (k+1) (s+n,t+n) := by
    convert hb using 1; congr 1; omega
  have hcycle : ReachesPage (background.classical.obj (Y.obj background.auxiliary))
      ((r:ℤ)-n+normalizedExponent background.classicalTower f) (s+n,t+n) (y+b) := by
    have hyr := (isCycle_iff_reaches background Y _ W.target_page_ge_two (s+n,t+n) y).mpr W.target_cycle
    exact (isCycle_iff_reaches background Y _ W.target_page_ge_two (s+n,t+n) (y+b)).mp
      (cycle_add_boundary Y _ _ _ y b hyr hb)
  have hp : (s+n,t+n,(t+n)-(k:ℤ))=
      (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f) := by
    ext <;> dsimp <;> omega
  have repr {A : SyntheticAdamsSS} {p p' : Tridegree} (h : p=p')
      (z : A.E₂ p) (e : (A.sequence.ssData p').eInfty) :
      HasInfinityRepresentative A 2 p' (regradeE2 h z) e ↔
        HasInfinityRepresentative A 2 p z
          ((eqToHom (congrArg (fun p => (A.sequence.ssData p).eInfty) h.symm)) e) := by
    subst p'
    simp only [regradeE2,eqToHom_refl,ModuleCat.id_apply]
  have hwrep := W.target_rep
  change HasInfinityRepresentative _ 2 _
    (regradeE2 hp (finiteTargetLabel background Y (r-1) (s+n) (t+n) k y)) W.target at hwrep
  have hnativ := (repr hp _ _).mp hwrep
  have hnew := finite_target_rep_add_boundary Y (r-1) k hkq (s+n) (t+n) y b hb' _ hnativ
  refine { W with target_cycle := hcycle, target_rep := ?_ }
  change HasInfinityRepresentative _ 2 _
    (regradeE2 hp (finiteTargetLabel background Y (r-1) (s+n) (t+n) k (y+b))) W.target
  exact (repr hp _ _).mpr hnew

private theorem suspension_desuspends_add (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (sx sb : Ambient background (.shift 1 X) (s,t))
    (x b : Ambient background X (s,t-1))
    (hx : (background.classicalSuspension X).DesuspendsClass s t sx x)
    (hb : (background.classicalSuspension X).DesuspendsClass s t sb b) :
    (background.classicalSuspension X).DesuspendsClass s t (sx+sb) (x+b) := by
  obtain ⟨a,c,ha,hc,hac⟩ := hx
  obtain ⟨a',c',ha',hc',hac'⟩ := hb
  refine ⟨a+a',c+c',?_,?_,?_⟩
  · rw [map_add,ha,ha']
  · rw [map_add,hc,hc']
  · simpa only [map_add,Submodule.coe_add] using congrArg₂ (fun x y => x+y) hac hac'

private theorem infinite_source_label_add (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t : ℤ)
    (x b : Ambient background X (s,t)) :
    infiniteSourceForExtension background X Y f s t (x+b)=
      infiniteSourceForExtension background X Y f s t x+
        infiniteSourceForExtension background X Y f s t b := by
  simp only [infiniteSourceForExtension,regradeE2,map_add]

/-- If both source labels admitted a positive extension, the normalized
leading E2 image of their exact boundary difference would have to vanish. -/
private theorem positive_extensions_force_boundary_image_zero (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (n s t : ℤ) (hn : 0<n)
    (x b : Ambient background X (s,t))
    (y y' : Ambient background Y (s+n,t+n))
    (hx : FiniteExtension background X Y f r n s t x y)
    (hxb : FiniteExtension background X Y f r n s t (x+b) y') :
    familyPageMap background.family (background.normalizedMap X Y f).map 2
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
      (infiniteSourceForExtension background X Y f s t b)=0 := by
  have h0 := positive_extension_map_e2_zero X Y f r n s t hn x y (Classical.choice hx)
  have h1 := positive_extension_map_e2_zero X Y f r n s t hn (x+b) y' (Classical.choice hxb)
  rw [infinite_source_label_add,map_add,h0,zero_add] at h1
  exact h1

private theorem nonzero_leading_image_no_positive_extension (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (n s t : ℤ) (hn : 0<n) (x : Ambient background X (s,t))
    (hx : familyPageMap background.family (background.normalizedMap X Y f).map 2
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
      (infiniteSourceForExtension background X Y f s t x)≠0) :
    ¬∃ y : Ambient background Y (s+n,t+n), FiniteExtension background X Y f r n s t x y := by
  rintro ⟨y,hy⟩
  exact hx (positive_extension_map_e2_zero X Y f r n s t hn x y (Classical.choice hy))

private theorem nonzero_boundary_image_obstructs_translation (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (r : ℕ) (n s t : ℤ) (hn : 0<n)
    (x b : Ambient background X (s,t))
    (y : Ambient background Y (s+n,t+n))
    (hx : FiniteExtension background X Y f r n s t x y)
    (hb : familyPageMap background.family (background.normalizedMap X Y f).map 2
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
      (infiniteSourceForExtension background X Y f s t b)≠0) :
    ¬∃ y' : Ambient background Y (s+n,t+n), FiniteExtension background X Y f r n s t (x+b) y' := by
  rintro ⟨y',hy'⟩
  exact hb (positive_extensions_force_boundary_image_zero X Y f r n s t hn x b y y' hx hy')


private abbrev mh2BoundaryClass : Ambient background .sphere (3,17) := oneLineTarget background 4

private theorem mh2BoundaryClass_differential :
    HasNonzeroDifferential background.classical.sphere 2 (1,16) (3,17)
      (background.standardClasses.standardHi 4) mh2BoundaryClass := by
  exact KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide) (by decide)

private theorem mh2BoundaryClass_nonzero : mh2BoundaryClass ≠ 0 := by
  intro hz
  obtain ⟨_,_,yr,_,hyr,_,hne⟩ := mh2BoundaryClass_differential
  apply hne
  rw [hz] at hyr
  exact represents_unique hyr (RepresentsOnPage.zero (by decide))

private theorem mh2BoundaryClass_boundary :
    mh2BoundaryClass ∈ boundaries background .sphere 2 (3,17) := by
  have hd : HasDifferential background.classical.sphere 2 (1,16) (3,17)
      (background.standardClasses.standardHi 4) mh2BoundaryClass := by
    obtain ⟨h,xr,yr,hx,hy,he,_⟩ := mh2BoundaryClass_differential
    exact ⟨h,xr,yr,hx,hy,he⟩
  exact represents_zero_mem_boundary background .sphere 3 (3,17) mh2BoundaryClass
    (differential_target_later_zero (by rw [background.classical.firstPage]) (by decide) hd)

private theorem sphere_ext_two_thirteen_zero (x : Ambient background .sphere (2,13)) : x=0 := by
  let e := KIP126.Computation.Standard.coordinates 2 13 (by decide)
  have hn : KIP126.Computation.Standard.archive.basisCount 2 13 = 0 :=
    (KIP126.Computation.Table.archive_dimension 2 13 (by decide)).trans (by decide)
  haveI : Subsingleton (Fin (KIP126.Computation.Standard.archive.basisCount 2 13) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  apply e.injective
  exact Subsingleton.elim _ _


end
end KIP126.ProofTools.Internal.Mahowald
