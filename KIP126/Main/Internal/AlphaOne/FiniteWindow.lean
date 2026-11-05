module

/- Complete finite-window calculation on the normalized fixed sphere sequence. -/
public import KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.Internal.AlphaOne.Quotients
import all KIP126.Main.Internal.AlphaOne.PageVanishing

/-! complete finite-window calculation. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.Computation.Table
open KIP126.AdamsSynthetic.Completed (background)
noncomputable section
universe v
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
private theorem stem123_middle_certificate_d3_s13_t137_basis2 : HasDifferential (Normalized.sphere) 3 (13,137) (16,139) (Normalized.basis .sphere 13 137 2) (Normalized.basis .sphere 16 139 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0]⟩ (by
    exact List.mem_of_getElem? (i := 108) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d2_s14_t138_basis1 : HasDifferential (Normalized.sphere) 2 (14,138) (16,139) (Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 1 + Normalized.basis .sphere 16 139 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2]⟩ (by
    exact List.mem_of_getElem? (i := 122) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d2_s14_t138_basis0_add_basis1 : HasDifferential (Normalized.sphere) 2 (14,138) (16,139) (Normalized.basis .sphere 14 138 0 + Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2]⟩ (by
    exact List.mem_of_getElem? (i := 123) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d3_s15_t138_basis2 : HasDifferential (Normalized.sphere) 3 (15,138) (18,140) (Normalized.basis .sphere 15 138 2) (Normalized.basis .sphere 18 140 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2]⟩ (by
    exact List.mem_of_getElem? (i := 117) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h



private theorem stem123_middle_certificate_d5_s10_t134_basis3 : HasDifferential (Normalized.sphere) 5 (10,134) (15,138) (Normalized.basis .sphere 10 134 3) (Normalized.basis .sphere 15 138 1) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1]⟩ (by
    exact List.mem_of_getElem? (i := 79) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d4_s11_t135_basis1_add_basis2 : HasDifferential (Normalized.sphere) 4 (11,135) (15,138) (Normalized.basis .sphere 11 135 1 + Normalized.basis .sphere 11 135 2) (Normalized.basis .sphere 15 138 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0]⟩ (by
    exact List.mem_of_getElem? (i := 89) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d3_s14_t137_basis1 : HasDifferential (Normalized.sphere) 3 (14,137) (17,139) (Normalized.basis .sphere 14 137 1) (Normalized.basis .sphere 17 139 1) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 14, 137, [1], 17, 139, [1]⟩ (by
    exact List.mem_of_getElem? (i := 112) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [1] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d3_s14_t137_basis0 : HasDifferential (Normalized.sphere) 3 (14,137) (17,139) (Normalized.basis .sphere 14 137 0) (Normalized.basis .sphere 17 139 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 14, 137, [0], 17, 139, [0]⟩ (by
    exact List.mem_of_getElem? (i := 113) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d2_s12_t136_basis2 : HasDifferential (Normalized.sphere) 2 (12,136) (14,137) (Normalized.basis .sphere 12 136 2) (Normalized.basis .sphere 14 137 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2]⟩ (by
    exact List.mem_of_getElem? (i := 99) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (12,136) (14,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d3_s13_t136_basis1 : HasDifferential (Normalized.sphere) 3 (13,136) (16,138) (Normalized.basis .sphere 13 136 1) (Normalized.basis .sphere 16 138 1) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 13, 136, [1], 16, 138, [1]⟩ (by
    exact List.mem_of_getElem? (i := 105) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [1] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d3_s13_t136_basis0 : HasDifferential (Normalized.sphere) 3 (13,136) (16,138) (Normalized.basis .sphere 13 136 0) (Normalized.basis .sphere 16 138 0 + Normalized.basis .sphere 16 138 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 13, 136, [0], 16, 138, [0, 2]⟩ (by
    exact List.mem_of_getElem? (i := 106) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [0, 2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d2_s11_t135_basis2 : HasDifferential (Normalized.sphere) 2 (11,135) (13,136) (Normalized.basis .sphere 11 135 2) (Normalized.basis .sphere 13 136 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2]⟩ (by
    exact List.mem_of_getElem? (i := 90) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (11,135) (13,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d3_s9_t133_basis1_add_basis2 : HasDifferential (Normalized.sphere) 3 (9,133) (12,135) (Normalized.basis .sphere 9 133 1 + Normalized.basis .sphere 9 133 2) (Normalized.basis .sphere 12 135 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 9, 133, [1, 2], 12, 135, [0]⟩ (by
    exact List.mem_of_getElem? (i := 63) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d3_s9_t133_basis0_add_basis2 : HasDifferential (Normalized.sphere) 3 (9,133) (12,135) (Normalized.basis .sphere 9 133 0 + Normalized.basis .sphere 9 133 2) (Normalized.basis .sphere 12 135 1 + Normalized.basis .sphere 12 135 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 3, 9, 133, [0, 2], 12, 135, [1, 2]⟩ (by
    exact List.mem_of_getElem? (i := 64) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_d5_s7_t131_basis1 : HasDifferential (Normalized.sphere) 5 (7,131) (12,135) (Normalized.basis .sphere 7 131 1) (Normalized.basis .sphere 12 135 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2]⟩ (by
    exact List.mem_of_getElem? (i := 43) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 5 (7,131) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_nonzero3
    :
    HasNonzeroDifferential (Normalized.sphere) 3 (15,138) (18,140)
      (Normalized.basis .sphere 15 138 2) (Normalized.basis .sphere 18 140 2) := by
  classical
  let E := Normalized.sphere
  obtain ⟨e16_139,he16_139⟩ := Normalized.basis_correct ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = Normalized.basis .sphere 16 139 i.val at he16_139
  obtain ⟨e18_140,he18_140⟩ := Normalized.basis_correct ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = Normalized.basis .sphere 18 140 i.val at he18_140
  have h324 : HasDifferential E 3 (13,137) (16,139) (Normalized.basis .sphere 13 137 2) (Normalized.basis .sphere 16 139 0) := stem123_middle_certificate_d3_s13_t137_basis2
  have h366 : HasDifferential E 2 (14,138) (16,139) (Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 1 + Normalized.basis .sphere 16 139 2) := stem123_middle_certificate_d2_s14_t138_basis1
  have h367 : HasDifferential E 2 (14,138) (16,139) (Normalized.basis .sphere 14 138 0 + Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 2) := stem123_middle_certificate_d2_s14_t138_basis0_add_basis1
  have h654 : HasDifferential E 3 (15,138) (18,140) (Normalized.basis .sphere 15 138 2) (Normalized.basis .sphere 18 140 2) := stem123_middle_certificate_d3_s15_t138_basis2
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d2_16 : E.d 2 (16,139)=0 := by
    obtain ⟨_,_,y0,_,hy0,_⟩ := h324
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
      (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have d12 : E.d 2 (16,139) (Normalized.basis .sphere 16 139 1 + Normalized.basis .sphere 16 139 2)=0 := by
      have hd := h366.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d2 : E.d 2 (16,139) (Normalized.basis .sphere 16 139 2)=0 := by
      have hd := h367.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d1 : E.d 2 (16,139) (Normalized.basis .sphere 16 139 1)=0 := by
      simpa only [map_add,d2,add_zero] using d12
    ext a
    change E.d 2 (16,139) a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
      (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]
  obtain ⟨_,a2,b2,ha2,hb2,hd2⟩ := h654
  change E.d 3 (15,138) a2=b2 at hd2
  have b2base : Normalized.basis .sphere 18 140 2 ≠ 0 := by
    intro h
    rw [show Normalized.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm] at h
    have hh := congrArg e18_140 h
    simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
    have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
    norm_num [Finsupp.single_apply] at hh'
  have b2ne : b2≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140))
    (by change (2:ℤ)≤2;omega) (by decide) d2_16 hb2 (hrep2 _) b2base
  exact ⟨by rfl,a2,b2,ha2,hb2,hd2,b2ne⟩




private theorem stem123_weight130_finite_quotients_d2_s10_t133_basis1 : HasDifferential (Normalized.sphere) 2 (10,133) (12,134)
    (Normalized.basis .sphere 10 133 1) (Normalized.basis .sphere 12 134 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,10,133,[1],12,134,[2]⟩ (by
    exact List.mem_of_getElem? (i := 77) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (10,133) (12,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s10_t133_basis0 : HasDifferential (Normalized.sphere) 2 (10,133) (12,134)
    (Normalized.basis .sphere 10 133 0) (Normalized.basis .sphere 12 134 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,10,133,[0],12,134,[2]⟩ (by
    exact List.mem_of_getElem? (i := 96) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (10,133) (12,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d3_s7_t131_basis0 : HasDifferential (Normalized.sphere) 3 (7,131) (10,133)
    (Normalized.basis .sphere 7 131 0) (Normalized.basis .sphere 10 133 0 + Normalized.basis .sphere 10 133 1) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1]⟩ (by
    exact List.mem_of_getElem? (i := 44) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (7,131) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s8_t132_basis0 : HasDifferential (Normalized.sphere) 2 (8,132) (10,133)
    (Normalized.basis .sphere 8 132 0) (Normalized.basis .sphere 10 133 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,8,132,[0],10,133,[2]⟩ (by
    exact List.mem_of_getElem? (i := 51) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (8,132) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d4_s11_t135_basis1_add_basis2 : HasDifferential (Normalized.sphere) 4 (11,135) (15,138)
    (Normalized.basis .sphere 11 135 1 + Normalized.basis .sphere 11 135 2) (Normalized.basis .sphere 15 138 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,4,11,135,[1, 2],15,138,[0]⟩ (by
    exact List.mem_of_getElem? (i := 89) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 4 (11,135) (15,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d5_s10_t134_basis3 : HasDifferential (Normalized.sphere) 5 (10,134) (15,138)
    (Normalized.basis .sphere 10 134 3) (Normalized.basis .sphere 15 138 1) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,5,10,134,[3],15,138,[1]⟩ (by
    exact List.mem_of_getElem? (i := 79) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 5 (10,134) (15,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd





private theorem stem123_weight130_finite_quotients_d3_s9_t133_basis1_add_basis2 : HasDifferential (Normalized.sphere) 3 (9,133) (12,135)
    (Normalized.basis .sphere 9 133 1 + Normalized.basis .sphere 9 133 2) (Normalized.basis .sphere 12 135 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,3,9,133,[1, 2],12,135,[0]⟩ (by
    exact List.mem_of_getElem? (i := 63) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (9,133) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d3_s9_t133_basis0_add_basis2 : HasDifferential (Normalized.sphere) 3 (9,133) (12,135)
    (Normalized.basis .sphere 9 133 0 + Normalized.basis .sphere 9 133 2) (Normalized.basis .sphere 12 135 1 + Normalized.basis .sphere 12 135 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,3,9,133,[0, 2],12,135,[1, 2]⟩ (by
    exact List.mem_of_getElem? (i := 64) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (9,133) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d5_s7_t131_basis1 : HasDifferential (Normalized.sphere) 5 (7,131) (12,135)
    (Normalized.basis .sphere 7 131 1) (Normalized.basis .sphere 12 135 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,5,7,131,[1],12,135,[2]⟩ (by
    exact List.mem_of_getElem? (i := 43) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 5 (7,131) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_boundary_of_zero_representative
    {r : ℤ} {p : ℤ×ℤ} {x : Normalized.sphere.Page 2 p}
    (hx : RepresentsOnPage (Normalized.sphere) r p x 0) :
    x ∈ boundaries (r-1) p := by
  classical
  let E := Normalized.sphere
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap ↑(r-2).toNat p = boundaryMap ↑(r-2).toNat p := by
    dsimp only [boundaryMap,cycleMap,boundaryMapFor,cycleMapFor,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz


private theorem stem123_weight130_finite_quotients_cycle_quotient_zero_of_page
    (r c b : ℤ) (p : ℤ×ℤ) (hr : 2≤r) (hc : r≤c+1) (hb : r-1≤b)
    (hz : Subsingleton ((Normalized.sphere).Page r p)) :
    Subsingleton (CycleQuotient c b p) := by
  apply quotient_subsingleton_of_le
  intro x hx
  obtain ⟨x',hx'⟩ := (cycles_reaches c p (by omega) x).mp hx
  obtain ⟨xr,hxr⟩ := represents_before hr hc hx'
  rw [hz.elim xr 0] at hxr
  exact boundaries_monotone p hb
    (stem123_weight130_finite_quotients_boundary_of_zero_representative hxr)


private theorem stem123_weight130_finite_quotients_cycle_differential_zero
    {r c : ℤ} {p : ℤ×ℤ} {x : Normalized.sphere.Page 2 p}
    {a : (Normalized.sphere).Page r p}
    (hr : 2≤r) (hc : r≤c)
    (hx : x∈cycles c p)
    (ha : RepresentsOnPage (Normalized.sphere) r p x a) :
    (Normalized.sphere).d r p a=0 := by
  classical
  obtain ⟨y,hy⟩ := (cycles_reaches c p (by omega) x).mp hx
  exact represents_d_zero_of_later hr (by omega : r<c+1) ha ⟨y,hy⟩


private theorem stem123_weight130_finite_quotients_nonzero_differential_not_cycle
    {r c : ℤ} {p q : ℤ×ℤ} {x : Normalized.sphere.Page 2 p} {y : Normalized.sphere.Page 2 q}
    (hr : 2≤r) (hc : r≤c)
    (hd : HasNonzeroDifferential (Normalized.sphere) r p q x y) :
    x∉cycles c p := by
  classical
  intro hx
  obtain ⟨rfl,a,b,ha,hb,hd,hne⟩ := hd
  simp only [eqToHom_refl,Category.comp_id] at hd
  exact hne (hd.symm.trans (stem123_weight130_finite_quotients_cycle_differential_zero hr hc hx ha))


private theorem stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
    {c b : ℤ} {p : ℤ×ℤ}
    (h : cycles c p ≤ boundaries b p) :
    Subsingleton (CycleQuotient c b p) := by
  exact quotient_subsingleton_of_le h


private theorem stem123_weight130_finite_quotients_basis_mem_submodule
    {V : Type v} [AddCommGroup V] [Module ℤ V] {N : ℕ}
    (e : V ≃ₗ[ℤ] (Fin N →₀ F2)) (B : Submodule ℤ V)
    (h : ∀ i, e.symm (Finsupp.single i 1)∈B) (x : V) : x∈B := by
  classical
  have all (f : Fin N →₀ F2) : e.symm f∈B := by
    induction f using Finsupp.induction with
    | zero => simpa only [map_zero] using B.zero_mem
    | @single_add i a f hi ha ih =>
      rw [map_add]
      apply B.add_mem _ ih
      fin_cases a
      · change e.symm (Finsupp.single i (0:F2))∈B
        simpa only [Finsupp.single_zero,map_zero] using B.zero_mem
      · change e.symm (Finsupp.single i (1:F2))∈B
        exact h i
  simpa only [LinearEquiv.symm_apply_apply] using all (e x)


private theorem stem123_weight130_finite_quotients_stem123_af10_quotient :
    Subsingleton (CycleQuotient 8 4 (10,133)) := by
  classical
  let E := Normalized.sphere
  have h245 : HasDifferential E 2 (10,133) (12,134)
      (Normalized.basis .sphere 10 133 1) (Normalized.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_d2_s10_t133_basis1
  have h294 : HasDifferential E 2 (10,133) (12,134)
      (Normalized.basis .sphere 10 133 0) (Normalized.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_d2_s10_t133_basis0
  have h244 : HasDifferential E 3 (7,131) (10,133)
      (Normalized.basis .sphere 7 131 0) (Normalized.basis .sphere 10 133 0 + Normalized.basis .sphere 10 133 1) := stem123_weight130_finite_quotients_d3_s7_t131_basis0
  have h243 : HasDifferential E 2 (8,132) (10,133)
      (Normalized.basis .sphere 8 132 0) (Normalized.basis .sphere 10 133 2) := stem123_weight130_finite_quotients_d2_s8_t132_basis0
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,10,133,["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 10 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = Normalized.basis .sphere 10 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = Normalized.basis .sphere 10 133 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = Normalized.basis .sphere 10 133 2 := he 2
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,12,134,["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 12 134 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = Normalized.basis .sphere 12 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = Normalized.basis .sphere 12 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = Normalized.basis .sphere 12 134 2 := hf 2
  let B := boundaries 4 (10,133)
  have b01 : Normalized.basis .sphere 10 133 0+Normalized.basis .sphere 10 133 1∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=5) (p:=(10,133))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide) h244)
  have z2 : RepresentsOnPage E 5 (10,133) (Normalized.basis .sphere 10 133 2) 0 :=
      differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h243
  have b2 : Normalized.basis .sphere 10 133 2∈B := stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=5) (p:=(10,133)) z2
  have rep2 (x : E.Page 2 (10,133)) : RepresentsOnPage E 2 (10,133) x x := by
    haveI : Epi ((E.ssData (10,133)).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData (10,133)).pageπ 0)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have hd0 : E.d 2 (10,133) (Normalized.basis .sphere 10 133 0)=Normalized.basis .sphere 12 134 2 := h294.eq_on_page_two.2
  have hd1 : E.d 2 (10,133) (Normalized.basis .sphere 10 133 1)=Normalized.basis .sphere 12 134 2 := h245.eq_on_page_two.2
  have hd2 : E.d 2 (10,133) (Normalized.basis .sphere 10 133 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
  have ne : Normalized.basis .sphere 12 134 2≠0 := by
    intro hh
    rw [show Normalized.basis .sphere 12 134 2=f.symm (Finsupp.single 2 1) from (hf 2).symm] at hh
    have hh' := congrArg (fun x=>f x 2) hh
    norm_num [Finsupp.single_apply] at hh'
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have hd : E.d 2 (10,133) x=0 := stem123_weight130_finite_quotients_cycle_differential_zero  (r:=2) (c:=8) (p:=(10,133)) (x:=x) (by decide) (by decide) hx (rep2 x)
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [hd1] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,add_zero] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [hd0] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,add_zero] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    rw [hxe]
    exact b01
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2] at hxe
    rw [hxe]
    exact B.add_mem b01 b2


private theorem stem123_weight130_finite_quotients_stem123_af15_quotient
    (h3 : HasNonzeroDifferential (Normalized.sphere) 3 (15,138) (18,140)
      (Normalized.basis .sphere 15 138 2) (Normalized.basis .sphere 18 140 2)) :
    Subsingleton (CycleQuotient 3 9 (15,138)) := by
  classical
  let E := Normalized.sphere
  have h351 : HasDifferential E 4 (11,135) (15,138)
      (Normalized.basis .sphere 11 135 1 + Normalized.basis .sphere 11 135 2) (Normalized.basis .sphere 15 138 0) := stem123_weight130_finite_quotients_d4_s11_t135_basis1_add_basis2
  have h352 : HasDifferential E 5 (10,134) (15,138)
      (Normalized.basis .sphere 10 134 3) (Normalized.basis .sphere 15 138 1) := stem123_weight130_finite_quotients_d5_s10_t134_basis3
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,15,138,["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 15 138 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = Normalized.basis .sphere 15 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = Normalized.basis .sphere 15 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = Normalized.basis .sphere 15 138 2 := he 2
  let B := boundaries 9 (15,138)
  let C := cycles 3 (15,138)
  have b0 : Normalized.basis .sphere 15 138 0∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=10)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤4;omega) (by decide) h351)
  have b1 : Normalized.basis .sphere 15 138 1∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=10)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤5;omega) (by decide) h352)
  have c0 : Normalized.basis .sphere 15 138 0∈C := boundaries_le_cycles (15,138) 9 3 b0
  have c1 : Normalized.basis .sphere 15 138 1∈C := boundaries_le_cycles (15,138) 9 3 b1
  have bad : Normalized.basis .sphere 15 138 2∉C := stem123_weight130_finite_quotients_nonzero_differential_not_cycle (by decide) (by decide) h3
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0' at hxe
  generalize hc1 : e x 1=c1' at hxe
  generalize hc2 : e x 2=c2' at hxe
  fin_cases c0' <;> fin_cases c1' <;> fin_cases c2'
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    rw [hxe]
    exact b1
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (c1)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    rw [hxe]
    exact b0
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (c0)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    rw [hxe]
    exact B.add_mem b0 b1
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (C.add_mem c0 c1)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh









end
end KIP126.Main.Internal.AlphaOne
end
