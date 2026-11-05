module

import KIP126.SSComputation
import all KIP126.Main.Internal.Moore.ConstructionRepresentative

/-! Permanence from the two specified survival inputs. -/

@[expose] section
namespace KIP126.Main.Internal.Moore

private theorem moore_h6_sq_permanent : KIP126.Main.H6SquarePermanent :=
  h6_sq_permanent_of_moore_inputs
    KIP126.SSComputation.Moore.bottom_source_cycles_four
    KIP126.SSComputation.Moore.v_cycles_eight

private theorem moore_eta_extension_excluded (hc3 : KIP126.Main.Stem126D6Vanishes) :
    ¬ KIP126.Main.EtaExtensionDetection :=
  eta_extension_excluded_of_six_representative
    KIP126.SSComputation.Moore.v_cycles_eight
    (moore_sixth_representative_of_inputs
      KIP126.SSComputation.Moore.bottom_source_cycles_four
      KIP126.SSComputation.Moore.v_cycles_eight) hc3

end KIP126.Main.Internal.Moore
end
