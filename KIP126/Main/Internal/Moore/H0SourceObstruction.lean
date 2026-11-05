module

import all KIP126.Main.Internal.Moore.SphereCrossing
import KIP126.AdamsComputation.Table.Dimensions
import KIP126.AdamsSynthetic.Completed.MappingOperations
import KIP126.AdamsSynthetic.Completed.ShiftOperations
import KIP126.ProofTools.Representatives

/-! The actual sphere source is not an h₀ multiple. The obstruction is its
nonzero d₂, whereas every possible h₀ preimage is a d₂ cycle. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Computation.Table KIP126.Computation.Standard
open KIP126.Main.Internal.Selected
open KIP126.AdamsSynthetic.Completed (background)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem pairing_d2_zero
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ×ℤ)}
    (P : SSPairing E E E) (p q u v r : ℤ×ℤ)
    (x : E.Page 2 p) (y : E.Page 2 q)
    (hx : HasDifferential E 2 p u x 0) (hy : HasDifferential E 2 q v y 0)
    (hur : u+q=r) (hvr : p+v=r) :
    HasDifferential E 2 (p+q) r (P.pair 2 p q x y) 0 := by
  obtain ⟨hdu,hdx⟩ := hx.eq_on_page_two
  obtain ⟨hdv,hdy⟩ := hy.eq_on_page_two
  subst u
  subst v
  subst r
  simp only [eqToHom_refl,Category.comp_id] at hdx hdy
  have hz : E.d 2 (p+q) (P.pair 2 p q x y)=0 := by
    rw [P.leibniz,hdx,hdy]
    simp
  refine ⟨by ac_rfl,_,0,RepresentsOnPage.self_two _,RepresentsOnPage.zero (by decide),?_⟩
  rw [ModuleCat.comp_apply,hz,map_zero]

private theorem sphere_product_d2_zero
    (p q u v r : ℤ×ℤ)
    (x : background.classical.sphere.Page 2 p)
    (y : background.classical.sphere.Page 2 q)
    (hx : HasDifferential background.classical.sphere 2 p u x 0)
    (hy : HasDifferential background.classical.sphere 2 q v y 0)
    (hur : u+q=r) (hvr : p+v=r) :
    HasDifferential background.classical.sphere 2 (p+q) r
      (background.sphereAlgebra.product p q x y) 0 := by
  let S : KIP126.AdamsSynthetic.Completed.FiniteSpectrum :=
    ⟨KIP126.StableHomotopy.SphereSpectrum,KIP126.AdamsSynthetic.IsFiniteSpectrum.sphere⟩
  let I := KIP126.AdamsSynthetic.sphereMappingAdamsIso
    KIP126.AdamsSynthetic.Completed.closedBackground background.classical
  let P := (KIP126.AdamsSynthetic.Completed.mapping_pairing S S S).ssPairing
  have hinv (r : ℤ) (p : ℤ×ℤ) (a : background.classical.sphere.Page r p) :
      I.hom.pageMap r p (I.inv.pageMap r p a)=a := by
    change (I.inv.pageMap r p≫I.hom.pageMap r p) a=a
    rw [←SpectralSequenceMorphism.pageMap_comp,I.inv_hom_id,SpectralSequenceMorphism.pageMap_id]
    rfl
  have hp (p q : ℤ×ℤ) (a) (b) :
      I.hom.pageMap 2 (p+q) (P.pair 2 p q a b)=
        background.sphereAlgebra.product p q (I.hom.pageMap 2 p a) (I.hom.pageMap 2 q b) :=
    KIP126.AdamsSynthetic.Completed.mapping_sphere_product p q a b
  have hx' := I.inv.hasDifferential hx
  have hy' := I.inv.hasDifferential hy
  simp only [map_zero] at hx' hy'
  have h := I.hom.hasDifferential (pairing_d2_zero P p q u v r
    (I.inv.pageMap 2 p x) (I.inv.pageMap 2 q y) hx' hy' hur hvr)
  simpa only [hp,hinv,map_zero] using h

private theorem sphere_h0_d2_zero :
    HasDifferential background.classical.sphere 2 (1,1) (3,2) h0 0 := by
  haveI : Subsingleton (background.classical.sphere.Page 2 (3,2)) := by
    let e := coordinates 3 2 (by decide)
    have hn : archive.basisCount 3 2=0 := (archive_dimension 3 2 (by decide)).trans (by decide)
    haveI : Subsingleton (Fin (archive.basisCount 3 2) →₀ ZMod 2) := by
      rw [hn]
      infer_instance
    exact e.injective.subsingleton
  apply hasDifferential_two_of_subsingleton_target _ h0
  simp only [background.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]

private theorem sphere_incoming_d2_zero : background.classical.sphere.d 2 (7,131)=0 := by
  have tr (E F : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=F)
      (hz : E.d 2 (7,131)=0) : F.d 2 (7,131)=0 := by
    cases h
    exact hz
  exact tr Normalized.sphere background.classical.sphere Normalized.sphere_eq
    SphereCrossing.incoming_d2_zero

private theorem sphere_incoming_d2_zero_on
    (y : background.classical.sphere.Page 2 (7,131)) :
    HasDifferential background.classical.sphere 2 (7,131) (9,132) y 0 := by
  have hdeg : (7,131)+background.classical.sphere.diffDeg 2=(9,132) := by
    simp only [background.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  refine ⟨hdeg,y,0,RepresentsOnPage.self_two _,RepresentsOnPage.zero (by decide),?_⟩
  rw [sphere_incoming_d2_zero,zero_comp]
  rfl

private theorem sphere_source_nonzero : basis .sphere 8 132 0≠0 := by
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,8,132,["367,1"]⟩
    (List.mem_of_getElem? (i := 160) rfl)
  change background.classical.sphere.Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1)=basis .sphere 8 132 0 := he 0
  intro hz
  rw [←he0] at hz
  have h : Finsupp.single (0:Fin 1) (1:F2)=0 := by
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using congrArg e hz
  have h0 := congrArg (fun f : Fin 1 →₀ F2 => f 0) h
  exact one_ne_zero (by simpa only [Finsupp.single_eq_same,Finsupp.zero_apply] using h0)

/-- The Moore noncancellation conclusion follows from the specified sphere input. -/
private theorem h0_source_not_in_image :
    ¬∃ y : background.classical.sphere.Page 2 (7,131),
      product (r := (8,132)) h0 y=basis .sphere 8 132 0 := by
  rintro ⟨y,hy⟩
  have hd := sphere_product_d2_zero (1,1) (7,131) (3,2) (9,132) (10,133)
    h0 y sphere_h0_d2_zero (sphere_incoming_d2_zero_on y) (by decide) (by decide)
  have hprod : background.sphereAlgebra.product (1,1) (7,131) h0 y=basis .sphere 8 132 0 := by
    change background.sphereAlgebra.product (1,1) (7,131) h0 y=basis .sphere 8 132 0 at hy
    exact hy
  rw [hprod] at hd
  change HasDifferential background.classical.sphere 2 (8,132) (10,133)
    (basis .sphere 8 132 0) 0 at hd
  obtain ⟨hdeg,heq⟩ := hd.eq_on_page_two
  have hz : background.classical.sphere.d 2 (8,132) (basis .sphere 8 132 0)=0 := by
    apply (ModuleCat.mono_iff_injective
      (eqToHom (congrArg (background.classical.sphere.Page 2) hdeg))).mp inferInstance
    simpa only [ModuleCat.comp_apply,map_zero] using heq
  have hr := (PageThree.reachesPage_iff_d2_eq_zero
    (by rw [background.classical.firstPage]) (8,132) (basis .sphere 8 132 0)).mpr hz
  have hc := ((KIP126.ProofTools.isCycle_iff_reaches background .sphere 3 (by decide)
    (8,132) (basis .sphere 8 132 0)).mpr hr).2
  change basis .sphere 8 132 0∈KIP126.Literature.cycles background .sphere 2 (8,132) at hc
  rw [SphereCrossing.cycles_two_source_eq_bot] at hc
  exact sphere_source_nonzero hc

end
end KIP126.Main.Internal.Moore
end
