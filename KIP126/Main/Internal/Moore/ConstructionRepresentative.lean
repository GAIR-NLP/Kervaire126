module

import all KIP126.Main.Internal.Moore.ConstructionExactness
import all KIP126.Main.Internal.Moore.ConstructionTopFiltration
import all KIP126.Main.Internal.Moore.ConstructionNonzero
import all KIP126.Main.Internal.Moore.ConstructionAction
import all KIP126.Main.Internal.Moore.ConstructionLayers
import all KIP126.Main.Internal.Moore.Reduction

/-! The Moore construction from its two explicit survival inputs. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.Main.Internal KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The actual nonzero Moore bottom source surviving through d₄ produces
an actual sphere Q₄ top image with the prescribed λV detector. -/
private theorem moore_fourth_top_detected
    (hcycle : KIP126.AdamsComputation.Moore.bottomSource ∈
      cycles background KIP126.AdamsComputation.Moore.adamsObject 4 (8,132)) :
    ∃ c4 : BiHom 124 132 (XModLambdaN
        (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4),
      FiltrationAtLeast background.syntheticTower 9 (mooreTopImage c4) ∧
      ¬ FiltrationAtLeast background.syntheticTower 10 (mooreTopImage c4) ∧
      Detects (background.convergence (.quotient 4 .sphere)) (9,132,131)
        (quotientLabel 4 9 132 1 KIP126.Computation.Standard.V) (mooreTopImage c4) := by
  obtain ⟨c4,hc4⟩ := moore_fourth_source_representative
    KIP126.AdamsComputation.Moore.bottomSource hcycle
  have h9 := moore_top_image_filtration_nine c4 hc4
  have h10 := moore_top_not_high KIP126.AdamsComputation.Moore.bottomSource
    moore_bottom_source_ne_zero c4 hc4
  exact ⟨c4,h9,h10,moore_actual_fourth_detection_of_not_high _ h9 h10⟩

/-- The two survival hypotheses supply the Q₆ witness. -/
private theorem moore_sixth_representative_of_inputs
    (hcycle : KIP126.AdamsComputation.Moore.bottomSource ∈
      cycles background KIP126.AdamsComputation.Moore.adamsObject 4 (8,132))
    (hV : KIP126.Computation.Standard.V ∈ cycles background .sphere 8 (9,132)) :
    ∃ b6 : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6),
      Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
        (quotientLabel 6 9 132 3 KIP126.Computation.Standard.V) b6 ∧
      sphereAction KIP126.Literature.Standard.syntheticH0 b6 = 0 := by
  obtain ⟨c4,h9,h10,_⟩ := moore_fourth_top_detected hcycle
  obtain ⟨a,ha9,ha10,hzero⟩ := moore_fourth_action_representative c4 h9 h10
  have hdet := moore_actual_fourth_detection_of_not_high a ha9 ha10
  have hV3 : KIP126.Computation.Standard.V ∈ cycles background .sphere 3 (9,132) :=
    cycles_antitone background .sphere (9,132) (by decide : (3:ℤ) ≤ 8) hV
  exact sixth_representative_of_fourth KIP126.Computation.Standard.V hV3 a hdet hzero

/-- Construction from the Moore source-survival hypothesis and V's E₉ survival,
with both computation conditions explicit. -/
private theorem h6_sq_permanent_of_moore_inputs
    (hcycle : KIP126.AdamsComputation.Moore.bottomSource ∈
      cycles background KIP126.AdamsComputation.Moore.adamsObject 4 (8,132))
    (hV : KIP126.Computation.Standard.V ∈ cycles background .sphere 8 (9,132)) :
    KIP126.Main.H6SquarePermanent :=
  h6_sq_permanent_of_six_representative hV
    (moore_sixth_representative_of_inputs hcycle hV)

end
end KIP126.Main.Internal.Moore
end
