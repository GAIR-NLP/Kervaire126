module

import KIP126.Main.H6SquarePermanent

/-! The obstruction exclusion supplied by the Moore construction. -/

@[expose] section
namespace KIP126.Main.SectionSeven

private theorem eta_extension_excluded_of_d6_vanishes
    (hc3 : KIP126.Main.Stem126D6Vanishes) : ¬ KIP126.Main.EtaExtensionDetection :=
  KIP126.Main.eta_extension_excluded_of_d6_vanishes hc3

end KIP126.Main.SectionSeven
end
