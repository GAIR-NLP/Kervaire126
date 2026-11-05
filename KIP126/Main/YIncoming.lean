module

public import KIP126.Main.DifferentialCriterion
import all KIP126.Main.Internal.ChoiceIndependence.Completion
import all KIP126.Main.Internal.NuNinth.Incoming
import all KIP126.Main.Internal.PageCalculus
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
import KIP126.AdamsComputation.Table.Values

/-! Fact 7.15 from the finite incoming window and Proposition 7.8.
The table and Main window give the finite exclusions; Proposition 7.8
excludes the possible ninth differential from h₆². -/

@[expose] section
namespace KIP126.Main.Internal.YIncoming
open CategoryTheory CategoryTheory.Limits
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Completed (background)
open KIP126.Computation.Standard KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem source_four_second_boundary :
    HasDifferential background.classical.sphere 2 (2,129) (4,130)
      (basis .sphere 2 129 0) (basis .sphere 4 130 1) := by
  have h := result ⟨.sphere,.equation,2,2,129,[0],4,130,[1]⟩
    (by exact List.mem_of_getElem? (i := 21) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 129 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 4 130 [1] = true := rfl
  dsimp only [decode] at ha hb
  simp only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at hd
  exact hd

private theorem source_seven_zero (z : background.classical.sphere.Page 7 (4,130)) : z = 0 := by
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,4,130,["341,1","0,2,69,2"]⟩
    (by exact List.mem_of_getElem? (i := 119) rfl)
  change background.classical.sphere.Page 2 (4,130) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = basis .sphere 4 130 i.val at he
  have source_binding : e.symm (Finsupp.single 0 1) = atom .x_126_4 := by
    rw [he 0]
    exact basis_value ⟨.named .x_126_4,0⟩ (by decide)
  have hnonzero := d3_x126_4
  rw [←source_binding] at hnonzero
  obtain ⟨hdeg,a,y,ha,hy,hd,hyn⟩ := hnonzero
  have hboundary : RepresentsOnPage background.classical.sphere 3 (4,130)
      (e.symm (Finsupp.single 1 1)) 0 := by
    rw [he 1]
    exact differential_target_later_zero (by rw [background.classical.firstPage])
      (by decide : (2:ℤ)<3) source_four_second_boundary
  obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤7) z
  obtain ⟨z3,hz3⟩ := represents_before (by decide : (2:ℤ)≤3)
    (by decide : (3:ℤ)≤7) hx
  have dz : background.classical.sphere.d 3 (4,130) z3 = 0 :=
    represents_d_zero_of_later (by rw [background.classical.firstPage]; decide)
      (by decide : (3:ℤ)<7) hz3 ⟨z,hx⟩
  have za : z3 = a → False := by
    intro h
    rw [h] at dz
    rw [ModuleCat.comp_apply,dz,map_zero] at hd
    exact hyn hd.symm
  have hz : z3 = 0 := by
    rcases generated_two (by decide : (2:ℤ)≤3) e a 0 ha hboundary z3 with h|h|h|h
    · exact h
    · exact (za h).elim
    · exact h
    · exact (za (by simpa only [add_zero] using h)).elim
  rw [hz] at hz3
  exact represents_later_zero (by decide : (3:ℤ)≤7) hz3 hx

private theorem empty_later {p : ℤ × ℤ} {r : ℤ} (hr : 2 ≤ r)
    (e : background.classical.sphere.Page 2 p ≃ₗ[ℤ] (Fin 0 →₀ F2))
    (z : background.classical.sphere.Page r p) : z = 0 := by
  haveI : Subsingleton (background.classical.sphere.Page 2 p) := e.injective.subsingleton
  obtain ⟨x,hx⟩ := page_has_initial_representative hr z
  rw [Subsingleton.elim x 0] at hx
  exact represents_unique hx (RepresentsOnPage.zero hr)

private theorem late_incoming (r : ℤ) (hr : 7 ≤ r)
    (hit : HitOnPage background.classical.sphere r (11,136) Y) :
    r = 9 ∧ HasNonzeroDifferential background.classical.sphere 9 (2,128) (11,136) h6Square Y := by
  rcases hit with ⟨⟨s,t⟩,hdeg,z,y,hy,hyn,hd⟩
  have hs : s = 11-r := by
    have h := congrArg Prod.fst hdeg
    simp only [KIP126.Classical.Adams.ClassicalAdamsFamily.sphere,
      KIP126.Classical.Adams.ClassicalAdamsFamily.obj,background.classical.differentialDegree,
      Prod.mk_add_mk] at h
    omega
  have ht : t = 137-r := by
    have h := congrArg Prod.snd hdeg
    simp only [KIP126.Classical.Adams.ClassicalAdamsFamily.sphere,
      KIP126.Classical.Adams.ClassicalAdamsFamily.obj,background.classical.differentialDegree,
      Prod.mk_add_mk] at h
    omega
  subst s
  subst t
  have zero_contra (hz : z = 0) : False := by
    rw [hz,ModuleCat.comp_apply,map_zero,map_zero] at hd
    exact hyn hd.symm
  by_cases hlate : 12 ≤ r
  · haveI : Subsingleton (background.classical.sphere.Page r (11-r,137-r)) :=
      KIP126.AdamsSynthetic.Completed.classical_page_negative .sphere r
        (11-r) (137-r) (by omega)
    exact (zero_contra (Subsingleton.elim _ _)).elim
  have hle : r ≤ 11 := by omega
  interval_cases r
  · exact (zero_contra (source_seven_zero z)).elim
  · have hz : background.classical.sphere.d 8 (11-8,137-8) z = 0 :=
      KIP126.Main.Internal.Choice.Completion.no_outgoing_126_three 8 (by decide) z
    rw [ModuleCat.comp_apply,hz,map_zero] at hd
    exact (hyn hd.symm).elim
  · obtain ⟨a,ha⟩ := page_has_initial_representative (by decide : (2:ℤ)≤9) z
    rcases square_exhaustive a with hz|hsquare
    · rw [hz] at ha
      exact (zero_contra (represents_unique ha (RepresentsOnPage.zero (by decide)))).elim
    · rw [hsquare] at ha
      exact ⟨rfl,hdeg,z,y,ha,hy,hd,hyn⟩
  · obtain ⟨e,_⟩ := basis_correct ⟨.sphere,1,127,[]⟩
      (by exact List.mem_of_getElem? (i := 90) rfl)
    exact (zero_contra (empty_later (by decide) e z)).elim
  · obtain ⟨e,_⟩ := basis_correct ⟨.sphere,0,126,[]⟩
      (by exact List.mem_of_getElem? (i := 77) rfl)
    exact (zero_contra (empty_later (by decide) e z)).elim

private theorem no_ninth :
    ¬ HasNonzeroDifferential background.classical.sphere 9 (2,128) (11,136) h6Square Y := by
  intro hd9
  have no_later (later : ReachesPage background.classical.sphere 12 (2,128) h6Square) : False := by
    obtain ⟨h,z,y,hz,hy,hd,hyn⟩ := hd9
    have dz := represents_d_zero_of_later
      (by rw [background.classical.firstPage]; decide) (by decide : (9:ℤ)<12) hz later
    rw [ModuleCat.comp_apply,dz,map_zero] at hd
    exact hyn hd.symm
  rcases KIP126.Main.h6_square_differential_dichotomy_and_criterion.1 with
    ⟨hp,_⟩ | ⟨hd12,_⟩
  · exact KIP126.Main.Internal.nonzero_differential_not_permanent
      (E := background.classical.sphere) (by rw [background.classical.firstPage]; decide) hd9 hp
  · obtain ⟨z,hz,_⟩ := hd12.source_survives
    exact no_later ⟨z,hz⟩

end
end KIP126.Main.Internal.YIncoming

namespace KIP126.Computation.Standard
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

/-- Fact 7.15: the table handles the finite window, and Proposition 7.8
excludes the remaining possible ninth-page incoming differential. -/
public theorem y_not_hit : NeverHit background.classical.sphere (11,136) Y := by
  intro r hr q h y hy hyn z hd
  have hit : HitOnPage background.classical.sphere r (11,136) Y := ⟨q,h,z,y,hy,hyn,hd⟩
  by_cases hearly : r ≤ 6
  · exact KIP126.Main.Internal.NuNinth.y_not_hit_through_six.2.2 r hr hearly hit
  · exact KIP126.Main.Internal.YIncoming.no_ninth
      (KIP126.Main.Internal.YIncoming.late_incoming r (by omega) hit).2

end KIP126.Computation.Standard
