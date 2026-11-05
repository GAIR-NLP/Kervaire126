module

import all KIP126.Main.Internal.AlphaOne.Quotients
import all KIP126.Main.Internal.Selected.NormalizedFacts
import all KIP126.Main.Internal.PageCalculus
import KIP126.SpectralSequence.FinitePageCalculus.Proofs
import KIP126.AdamsComputation.Table.Values

/-! The two-dimensional sphere crossing calculation from the specified
low-page rows. -/
@[expose] section
namespace KIP126.Main.Internal.Moore.SphereCrossing
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.Computation.Table
open KIP126.AdamsSynthetic.Completed (background)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private abbrev E := Normalized.sphere
private abbrev b := Normalized.basis .sphere

private theorem source0_d3 : HasDifferential E 3 (9,132) (12,134)
    (b 9 132 0) (b 12 134 1) := by
  have h := Normalized.result ⟨.sphere,.equation,3,9,132,[0],12,134,[1]⟩
    (List.mem_of_getElem? (i := 97) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem source1_d3 : HasDifferential E 3 (9,132) (12,134)
    (b 9 132 1) (b 12 134 1 + b 12 134 2) := by
  have h := Normalized.result ⟨.sphere,.equation,3,9,132,[1],12,134,[1, 2]⟩
    (List.mem_of_getElem? (i := 62) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem target0_d2 : HasDifferential E 2 (10,133) (12,134)
    (b 10 133 0) (b 12 134 2) := by
  have h := Normalized.result ⟨.sphere,.equation,2,10,133,[0],12,134,[2]⟩
    (List.mem_of_getElem? (i := 96) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem target1_d2 : HasDifferential E 2 (10,133) (12,134)
    (b 10 133 1) (b 12 134 2) := by
  have h := Normalized.result ⟨.sphere,.equation,2,10,133,[1],12,134,[2]⟩
    (List.mem_of_getElem? (i := 77) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem target2_hit : HasDifferential E 2 (8,132) (10,133)
    (b 8 132 0) (b 10 133 2) := by
  have h := Normalized.result ⟨.sphere,.equation,2,8,132,[0],10,133,[2]⟩
    (List.mem_of_getElem? (i := 51) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem incoming0_d3 : HasDifferential E 3 (7,131) (10,133)
    (b 7 131 0) (b 10 133 0 + b 10 133 1) := by
  have h := Normalized.result ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1]⟩
    (List.mem_of_getElem? (i := 44) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem incoming1_d5 : HasDifferential E 5 (7,131) (12,135)
    (b 7 131 1) (b 12 135 2) := by
  have h := Normalized.result ⟨.sphere,.equation,5,7,131,[1],12,135,[2]⟩
    (List.mem_of_getElem? (i := 43) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem incoming2_hit : HasDifferential E 2 (5,130) (7,131)
    (b 5 130 0) (b 7 131 2) := by
  have h := Normalized.result ⟨.sphere,.equation,2,5,130,[0],7,131,[2]⟩
    (List.mem_of_getElem? (i := 32) rfl)
  obtain ⟨a,ha,c,hc,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
  rw [←ha,←hc] at hd
  exact hd

private theorem source_basis :
    ∃ e : E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=b 9 132 i.val := by
  exact Normalized.basis_correct ⟨.sphere,9,132,["366,1","0,1,352,1"]⟩
    (List.mem_of_getElem? (i := 171) rfl)

private theorem incoming_basis :
    ∃ e : E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=b 7 131 i.val := by
  exact Normalized.basis_correct ⟨.sphere,7,131,["353,1","69,1,75,1","0,1,339,1"]⟩
    (List.mem_of_getElem? (i := 148) rfl)

private theorem target_incoming_basis :
    ∃ e : E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=b 10 133 i.val := by
  exact Normalized.basis_correct ⟨.sphere,10,133,["372,1","69,1,80,1","0,1,366,1"]⟩
    (List.mem_of_getElem? (i := 180) rfl)

private theorem target_basis :
    ∃ e : E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=b 12 134 i.val := by
  exact Normalized.basis_correct ⟨.sphere,12,134,["18,1,188,1","0,1,371,1","0,1,69,1,79,1"]⟩
    (List.mem_of_getElem? (i := 198) rfl)

private theorem incoming_d2_zero : E.d 2 (7,131)=0 := by
  obtain ⟨e,he⟩ := incoming_basis
  obtain ⟨_,a0,_,ha0,_,_⟩ := incoming0_d3
  obtain ⟨_,a1,_,ha1,_,_⟩ := incoming1_d5
  have h2 : RepresentsOnPage E 3 (7,131) (b 7 131 2) 0 :=
    differential_target_later_zero (by decide) (by decide) incoming2_hit
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e
  intro i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  rw [he i]
  fin_cases i
  · exact represents_d_zero_of_later (by decide) (by decide : (2:ℤ)<3)
      (represents_two_self _) ⟨a0,ha0⟩
  · exact represents_d_zero_of_later (by decide) (by decide : (2:ℤ)<5)
      (represents_two_self _) ⟨a1,ha1⟩
  · exact represents_d_zero_of_later (by decide) (by decide : (2:ℤ)<3)
      (represents_two_self _) ⟨0,h2⟩

private theorem target_d2_coordinate_one_zero
    (f : E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2))
    (hf : ∀ i, f.symm (Finsupp.single i 1)=b 12 134 i.val)
    (z : E.Page 2 (10,133)) : f (E.d 2 (10,133) z) 1=0 := by
  classical
  obtain ⟨e,he⟩ := target_incoming_basis
  have hd0 : E.d 2 (10,133) (b 10 133 0)=b 12 134 2 := target0_d2.eq_on_page_two.2
  have hd1 : E.d 2 (10,133) (b 10 133 1)=b 12 134 2 := target1_d2.eq_on_page_two.2
  have h2 : RepresentsOnPage E 3 (10,133) (b 10 133 2) 0 :=
    differential_target_later_zero (by decide) (by decide) target2_hit
  have hd2 : E.d 2 (10,133) (b 10 133 2)=0 :=
    represents_d_zero_of_later (by decide) (by decide : (2:ℤ)<3) (represents_two_self _) ⟨0,h2⟩
  have hf2' : f.symm (Finsupp.single (2:Fin 3) 1)=b 12 134 2 := hf 2
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1)=b 10 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1)=b 10 133 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1)=b 10 133 2 := he 2
  have hf2 : f (b 12 134 2) 1=0 := by
    rw [←hf2',LinearEquiv.apply_symm_apply]
    simp
  have heq : e z=Finsupp.single 0 (e z 0)+Finsupp.single 1 (e z 1)+Finsupp.single 2 (e z 2) := by
    ext i
    fin_cases i <;> simp
  have hz : z=e.symm (Finsupp.single 0 (e z 0)+Finsupp.single 1 (e z 1)+Finsupp.single 2 (e z 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e z 0=c0 at hz
  generalize hc1 : e z 1=c1 at hz
  generalize hc2 : e z 2=c2 at hz
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change z=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]
  · change z=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]
  · change z=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]
  · change z=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]
  · change z=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]
  · change z=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]
  · change z=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]
  · change z=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hz
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hz
    rw [hz]
    simp only [map_add,map_zero,hd0,hd1,hd2,Finsupp.add_apply,Finsupp.zero_apply,hf2,add_zero,zero_add]

private theorem target_basis1_third_nonzero
    {y : E.Page 3 (12,134)} (hy : RepresentsOnPage E 3 (12,134) (b 12 134 1) y) : y≠0 := by
  obtain ⟨f,hf⟩ := target_basis
  apply represents_next_nonzero_of_not_incoming (r := 2) (q := (10,133))
    (by decide) (by decide) hy (represents_two_self _)
  intro z hz
  have h := congrArg (fun a => f a 1) hz
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1)=b 12 134 1 := hf 1
  have htarget : f (b 12 134 1) 1=1 := by rw [←hf1,LinearEquiv.apply_symm_apply]; simp
  rw [target_d2_coordinate_one_zero f hf z,htarget] at h
  exact zero_ne_one h

private theorem target_sum_third_nonzero
    {y : E.Page 3 (12,134)} (hy : RepresentsOnPage E 3 (12,134) (b 12 134 1+b 12 134 2) y) : y≠0 := by
  obtain ⟨f,hf⟩ := target_basis
  apply represents_next_nonzero_of_not_incoming (r := 2) (q := (10,133))
    (by decide) (by decide) hy (represents_two_self _)
  intro z hz
  have h := congrArg (fun a => f a 1) hz
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1)=b 12 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1)=b 12 134 2 := hf 2
  have htarget : f (b 12 134 1+b 12 134 2) 1=1 := by
    rw [←hf1,←hf2,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    simp
  rw [target_d2_coordinate_one_zero f hf z,htarget] at h
  exact zero_ne_one h

private theorem source0_not_reaches_four : ¬ReachesPage E 4 (9,132) (b 9 132 0) := by
  intro hh
  obtain ⟨_,x,y,hx,hy,hd⟩ := source0_d3
  have hz := represents_d_zero_of_later (by decide) (by decide : (3:ℤ)<4) hx hh
  apply target_basis1_third_nonzero hy
  change E.d 3 (9,132) x=y at hd
  exact hd.symm.trans hz

private theorem source1_not_reaches_four : ¬ReachesPage E 4 (9,132) (b 9 132 1) := by
  intro hh
  obtain ⟨_,x,y,hx,hy,hd⟩ := source1_d3
  have hz := represents_d_zero_of_later (by decide) (by decide : (3:ℤ)<4) hx hh
  apply target_sum_third_nonzero hy
  change E.d 3 (9,132) x=y at hd
  exact hd.symm.trans hz

private theorem normalized_cycles_three_cases
    (x : E.Page 2 (9,132))
    (hx : x∈KIP126.Main.Internal.AlphaOne.cycles 3 (9,132)) :
    x=0 ∨ x=b 9 132 0+b 9 132 1 := by
  classical
  obtain ⟨e,he⟩ := source_basis
  have hr := (KIP126.Main.Internal.AlphaOne.cycles_reaches 3 (9,132) (by decide) x).mp hx
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1)=b 9 132 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1)=b 9 132 1 := he 1
  fin_cases c0 <;> fin_cases c1
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)) at hxe
    left
    simpa using hxe
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)) at hxe
    exfalso
    have hx1 : x=b 9 132 1 := by simpa only [Finsupp.single_zero,map_add,map_zero,zero_add,he1] using hxe
    exact source1_not_reaches_four (hx1 ▸ hr)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)) at hxe
    exfalso
    have hx0 : x=b 9 132 0 := by simpa only [Finsupp.single_zero,map_add,map_zero,add_zero,he0] using hxe
    exact source0_not_reaches_four (hx0 ▸ hr)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)) at hxe
    right
    simpa only [map_add,he0,he1] using hxe

private theorem normalized_boundaries_two_eq_bot :
    KIP126.Main.Internal.AlphaOne.boundaries 2 (9,132)=⊥ := by
  have hB : (E.ssData (9,132)).B 1=(E.ssData (9,132)).B 0 :=
    boundaries_succ_of_zero E 2 (by decide) (7,131) incoming_d2_zero
  have hzero : KIP126.Main.Internal.AlphaOne.boundaryMap 0 (9,132)=0 := by
    dsimp only [KIP126.Main.Internal.AlphaOne.boundaryMap,
      KIP126.Main.Internal.AlphaOne.boundaryMapFor]
    rw [←Category.assoc]
    simp [SSData.pageπ]
  have hfactor : KIP126.Main.Internal.AlphaOne.boundaryMap 1 (9,132)=
      Subobject.ofLE _ _ (le_of_eq hB) ≫
        KIP126.Main.Internal.AlphaOne.boundaryMap 0 (9,132) := by
    dsimp only [KIP126.Main.Internal.AlphaOne.boundaryMap,
      KIP126.Main.Internal.AlphaOne.boundaryMapFor]
    simp only [←Category.assoc,Subobject.ofLE_comp_ofLE]
  apply le_antisymm _ bot_le
  rintro x ⟨z,hz⟩
  change x=0
  change KIP126.Main.Internal.AlphaOne.boundaryMap 1 (9,132) z=x at hz
  rw [hfactor,hzero,comp_zero] at hz
  simpa using hz.symm

private theorem v_basis : KIP126.Computation.Standard.V=
    KIP126.Computation.Table.basis .sphere 9 132 0+
      KIP126.Computation.Table.basis .sphere 9 132 1 := by
  open KIP126.Computation.Standard in
  have v0 := basis_value ⟨.named .x_123_9,0⟩ (by decide)
  change KIP126.Computation.Table.basis .sphere 9 132 0=KIP126.Computation.Standard.atom .x_123_9 at v0
  have v1 : KIP126.Computation.Table.basis .sphere 9 132 1=
      KIP126.Computation.Standard.product (r := (9,132)) KIP126.Computation.Standard.h0
        (KIP126.Computation.Standard.atom .x_123_8) := by
    have h := basis_value ⟨.mul (.named .h0) (.named .x_123_8),1⟩ (by decide)
    simpa only [Expression.value,Expression.degree,KIP126.Computation.Standard.atom_h0] using h
  dsimp only [KIP126.Computation.Standard.V]
  rw [←v0,←v1]

private theorem normalized_v_label :
    Normalized.label (9,132) KIP126.Computation.Standard.V=b 9 132 0+b 9 132 1 := by
  rw [v_basis]
  exact map_add _ _ _

/-- The second-boundary submodule is zero in the actual sphere E₂ page. -/
private theorem boundaries_two_eq_bot :
    KIP126.Literature.boundaries background .sphere 2 (9,132)=⊥ := by
  let B (F : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (hr : F.r₀=2) :=
    LinearMap.range (KIP126.Main.Internal.AlphaOne.boundaryMapFor F hr 1 (9,132)).hom
  have tr (F F' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (he : F=F') (hr : F.r₀=2) (h : B F' (he ▸ hr)=⊥) : B F hr=⊥ := by
    cases he
    exact h
  exact tr background.classical.sphere E Normalized.sphere_eq.symm
    (background.classical.firstPage _) normalized_boundaries_two_eq_bot

/-- Every third-cycle label in this degree is either zero or the fixed V.
Together with the zero-boundary result this is the crossing restriction used
by the Moore construction. -/
private theorem cycles_three_cases
    (x : background.classical.sphere.Page 2 (9,132))
    (hx : x∈KIP126.Literature.cycles background .sphere 3 (9,132)) :
    x=0 ∨ x=KIP126.Computation.Standard.V := by
  let Z (F : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (hr : F.r₀=2) :=
    LinearMap.range (KIP126.Main.Internal.AlphaOne.cycleMapFor F hr 2 (9,132)).hom
  let P (F : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (hr : F.r₀=2) (v : F.Page 2 (9,132)) :=
    ∀ a : F.Page 2 (9,132), a∈Z F hr → a=0 ∨ a=v
  have hn : P E rfl (Normalized.label (9,132) KIP126.Computation.Standard.V) := by
    intro a ha
    rw [normalized_v_label]
    exact normalized_cycles_three_cases a ha
  have tr (F F' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (he : F=F') (hr : F.r₀=2) (v : F.Page 2 (9,132))
      (h : P F' (he ▸ hr)
        ((eqToHom (congrArg (fun S => S.Page 2 (9,132)) he)) v)) : P F hr v := by
    cases he
    simpa only [eqToHom_refl,ModuleCat.id_apply] using h
  exact tr background.classical.sphere E Normalized.sphere_eq.symm
    (background.classical.firstPage _) KIP126.Computation.Standard.V hn x hx

/-- The unique E₂ source basis vector has a nonzero d₂, so there are no
second cycles at the bottom degree of the Moore source. -/
private theorem normalized_cycles_two_source_eq_bot :
    KIP126.Main.Internal.AlphaOne.cycles 2 (8,132)=⊥ := by
  classical
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,8,132,["367,1"]⟩
    (List.mem_of_getElem? (i := 160) rfl)
  change E.Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1)=b 8 132 0 := he 0
  obtain ⟨f,hf⟩ := target_incoming_basis
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1)=b 10 133 2 := hf 2
  have hn : b 10 133 2≠0 := by
    intro hz
    have h := congrArg (fun z => f z 2) hz
    rw [←hf2,LinearEquiv.apply_symm_apply,map_zero] at h
    norm_num [Finsupp.single_apply] at h
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  have hr := (KIP126.Main.Internal.AlphaOne.cycles_reaches 2 (8,132)
    (by decide) x).mp hx
  have hd : E.d 2 (8,132) x=0 :=
    represents_d_zero_of_later (by decide) (by decide : (2:ℤ)<3)
      (represents_two_self x) hr
  have heq : e x=Finsupp.single 0 (e x 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc : e x 0=c at hxe
  fin_cases c
  · change x=e.symm (Finsupp.single 0 (0:F2)) at hxe
    simpa only [Finsupp.single_zero,map_zero] using hxe
  · change x=e.symm (Finsupp.single 0 (1:F2)) at hxe
    rw [he0] at hxe
    exfalso
    apply hn
    have hd0 : E.d 2 (8,132) (b 8 132 0)=b 10 133 2 := target2_hit.eq_on_page_two.2
    rw [hxe,hd0] at hd
    exact hd

private theorem cycles_two_source_eq_bot :
    KIP126.Literature.cycles background .sphere 2 (8,132)=⊥ := by
  let Z (F : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (hr : F.r₀=2) :=
    LinearMap.range (KIP126.Main.Internal.AlphaOne.cycleMapFor F hr 1 (8,132)).hom
  have tr (F F' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (he : F=F') (hr : F.r₀=2) (h : Z F' (he ▸ hr)=⊥) : Z F hr=⊥ := by
    cases he
    exact h
  exact tr background.classical.sphere E Normalized.sphere_eq.symm
    (background.classical.firstPage _) normalized_cycles_two_source_eq_bot

end
end KIP126.Main.Internal.Moore.SphereCrossing
end
