module
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.NuThree.Assembly
import all KIP126.Main.Internal.NuNinth.Lift
/-! The ν₉ extension obtained from the ν₃ and ν₅ extensions. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open KIP126.Main.SectionSeven
private theorem nu_extension_in_ninth_quotient :
    NuExtension9 KIP126.Computation.Standard.X KIP126.Computation.Standard.Y hopfNu :=
  nu_ninth_of_fifth_complete hopfNu NuThree.nu_extension_in_fifth_quotient
end KIP126.Main.Internal.NuNinth
