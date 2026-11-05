module

import all KIP126.AdamsComputation.Internal.SphereArchive.Basic
import all KIP126.AdamsComputation.Internal.SphereArchive.Generators

/-! Ordered S⁰ basis monomials in internal degrees 64–127.
Standard supplies their Adams E₂ interpretation. -/

@[expose] section
namespace KIP126.Computation.StandardArchive
open KIP126.Computation
set_option backward.privateInPublic true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private noncomputable def archiveMonomialRows64 : BasisRows generators 64 0 :=
  .cons [] (
  .cons [archiveGenerator69] (
  .cons [(.mul archiveGenerator18 archiveGenerator18)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator68] (
  .cons [archiveGenerator67] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator66,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator18)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator64)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator20))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator40))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator39)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator17)))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator65] (
  .cons [(.mul archiveGenerator1 archiveGenerator62)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows65 : BasisRows generators 65 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator69)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator18))] (
  .cons [archiveGenerator70] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator68)] (
  .cons [(.mul archiveGenerator18 archiveGenerator20),
      (.mul archiveGenerator0 archiveGenerator67)] (
  .cons [(.mul archiveGenerator18 archiveGenerator19)] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator64),
      (.mul archiveGenerator0 archiveGenerator66)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator64))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator40)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator39))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator17))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator65)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows66 : BasisRows generators 66 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator69)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator18)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator18)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator68))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator20)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator67))] (
  .cons [archiveGenerator72,
      (.mul archiveGenerator13 archiveGenerator33)] (
  .cons [(.mul archiveGenerator13 archiveGenerator32)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator66))] (
  .cons [(.mul archiveGenerator8 archiveGenerator42),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator64)))] (
  .cons [(.mul archiveGenerator16 archiveGenerator23)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59))))))] (
  .cons [archiveGenerator71] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator65))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows67 : BasisRows generators 67 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))] (
  .cons [archiveGenerator76,
      (.mul archiveGenerator1 archiveGenerator70),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator18))))] (
  .cons [archiveGenerator75,
      archiveGenerator74] (
  .cons [archiveGenerator73] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator20)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator72)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator64))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator66)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator64))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59)))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator71)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows68 : BasisRows generators 68 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator69)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator18)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator69))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator18)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator18 archiveGenerator24),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator18)))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator75),
      (.mul archiveGenerator0 archiveGenerator74)] (
  .cons [(.mul archiveGenerator0 archiveGenerator73)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator72)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator72))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator66))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator64)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator71),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator71))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows69 : BasisRows generators 69 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator18)))] (
  .cons [(.mul archiveGenerator2 archiveGenerator70)] (
  .cons [(.mul archiveGenerator1 archiveGenerator76),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator18))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator74))] (
  .cons [archiveGenerator80,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator73))] (
  .cons [archiveGenerator79] (
  .cons [] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13))] (
  .cons [(.mul archiveGenerator8 archiveGenerator46),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator72)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator45)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator66)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator64))))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator78] (
  .cons [archiveGenerator77] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59)))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows70 : BasisRows generators 70 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator18))))] (
  .cons [archiveGenerator86] (
  .cons [archiveGenerator85,
      archiveGenerator84,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))] (
  .cons [archiveGenerator83,
      archiveGenerator82,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator18)))))))] (
  .cons [archiveGenerator81] (
  .cons [(.mul archiveGenerator0 archiveGenerator80)] (
  .cons [(.mul archiveGenerator0 archiveGenerator79)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator66))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator64)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator78)] (
  .cons [(.mul archiveGenerator0 archiveGenerator77)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator71))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows71 : BasisRows generators 71 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator76)] (
  .cons [(.mul archiveGenerator2 archiveGenerator75),
      (.mul archiveGenerator0 archiveGenerator86)] (
  .cons [(.mul archiveGenerator0 archiveGenerator84),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator18))))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator81)] (
  .cons [(.mul archiveGenerator1 archiveGenerator79),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator80))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator79))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator66)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator64))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator78))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator77))] (
  .cons [archiveGenerator87] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator59)))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows72 : BasisRows generators 72 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator3 archiveGenerator69)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator69))] (
  .cons [archiveGenerator94] (
  .cons [archiveGenerator93,
      archiveGenerator92] (
  .cons [archiveGenerator91] (
  .cons [(.mul archiveGenerator3 archiveGenerator68),
      (.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator24))] (
  .cons [(.mul archiveGenerator3 archiveGenerator67),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator75)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator86))] (
  .cons [(.mul archiveGenerator1 archiveGenerator82),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator84)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))] (
  .cons [archiveGenerator90,
      archiveGenerator89,
      (.mul archiveGenerator1 archiveGenerator81)] (
  .cons [(.mul archiveGenerator23 archiveGenerator24),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator81))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator80)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator51)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator23))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator22))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator8)))] (
  .cons [archiveGenerator88] (
  .cons [] (
  .cons [(.mul archiveGenerator8 archiveGenerator50)] (
  .cons [(.mul archiveGenerator8 archiveGenerator49)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator77)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows73 : BasisRows generators 73 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator69))] (
  .cons [archiveGenerator96] (
  .cons [(.mul archiveGenerator0 archiveGenerator94)] (
  .cons [(.mul archiveGenerator0 archiveGenerator93),
      (.mul archiveGenerator0 archiveGenerator92)] (
  .cons [archiveGenerator95,
      (.mul archiveGenerator0 archiveGenerator91)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator68))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator67))] (
  .cons [(.mul archiveGenerator2 archiveGenerator80),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator90),
      (.mul archiveGenerator0 archiveGenerator89)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator81)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator80))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator50))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator49))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator87)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows74 : BasisRows generators 74 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator69))] (
  .cons [archiveGenerator99,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator96)] (
  .cons [(.mul archiveGenerator1 archiveGenerator92)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator92))] (
  .cons [(.mul archiveGenerator0 archiveGenerator95)] (
  .cons [(.mul archiveGenerator2 archiveGenerator82),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator68)))] (
  .cons [archiveGenerator98,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator67)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator81)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator80)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator89))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator81))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator80)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator88)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator49)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator97] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows75 : BasisRows generators 75 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator4 archiveGenerator69)] (
  .cons [(.mul archiveGenerator1 archiveGenerator96),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator3 archiveGenerator76),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator96))] (
  .cons [(.mul archiveGenerator3 archiveGenerator74),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator76))] (
  .cons [(.mul archiveGenerator1 archiveGenerator95)] (
  .cons [] (
  .cons [archiveGenerator101] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator51),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator23))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator29))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator9)))] (
  .cons [archiveGenerator100] (
  .cons [(.mul archiveGenerator17 archiveGenerator40)] (
  .cons [(.mul archiveGenerator8 archiveGenerator56)] (
  .cons [(.mul archiveGenerator8 archiveGenerator55)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows76 : BasisRows generators 76 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator99)] (
  .cons [(.mul archiveGenerator2 archiveGenerator92)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator96)))] (
  .cons [archiveGenerator107,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator74))] (
  .cons [archiveGenerator106,
      archiveGenerator105] (
  .cons [archiveGenerator104,
      archiveGenerator103] (
  .cons [(.mul archiveGenerator1 archiveGenerator98),
      (.mul archiveGenerator0 archiveGenerator101)] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator40))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator56))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator55))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator102] (
  .cons [(.mul archiveGenerator1 archiveGenerator97)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows77 : BasisRows generators 77 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator4 archiveGenerator69))] (
  .cons [archiveGenerator109,
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator96))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator76)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator92))] (
  .cons [archiveGenerator108,
      (.mul archiveGenerator2 archiveGenerator95)] (
  .cons [(.mul archiveGenerator0 archiveGenerator107)] (
  .cons [(.mul archiveGenerator0 archiveGenerator106)] (
  .cons [(.mul archiveGenerator0 archiveGenerator104),
      (.mul archiveGenerator0 archiveGenerator103)] (
  .cons [(.mul archiveGenerator18 archiveGenerator40),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator101))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))] (
  .cons [(.mul archiveGenerator5 archiveGenerator64),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator56)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator55)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator102)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows78 : BasisRows generators 78 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator69)] (
  .cons [(.mul archiveGenerator0 archiveGenerator109)] (
  .cons [(.mul archiveGenerator3 archiveGenerator84)] (
  .cons [(.mul archiveGenerator1 archiveGenerator107),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator95))] (
  .cons [(.mul archiveGenerator1 archiveGenerator105),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator107))] (
  .cons [archiveGenerator114,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator106))] (
  .cons [(.mul archiveGenerator13 archiveGenerator52),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator103))] (
  .cons [archiveGenerator113,
      (.mul archiveGenerator13 archiveGenerator51)] (
  .cons [archiveGenerator112,
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator23))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator32)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator13))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator60)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator17))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator111] (
  .cons [archiveGenerator110] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator102))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows79 : BasisRows generators 79 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator108)] (
  .cons [archiveGenerator115] (
  .cons [(.mul archiveGenerator2 archiveGenerator101),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator107)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator106)))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator113)] (
  .cons [(.mul archiveGenerator0 archiveGenerator112)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator64)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator111)] (
  .cons [(.mul archiveGenerator0 archiveGenerator110)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows80 : BasisRows generators 80 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator7 archiveGenerator69)] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator69))] (
  .cons [] (
  .cons [(.mul archiveGenerator3 archiveGenerator94)] (
  .cons [(.mul archiveGenerator6 archiveGenerator69),
      (.mul archiveGenerator3 archiveGenerator93)] (
  .cons [(.mul archiveGenerator7 archiveGenerator68),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator92)),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator69))] (
  .cons [(.mul archiveGenerator7 archiveGenerator67),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator68))] (
  .cons [(.mul archiveGenerator2 archiveGenerator107)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator107))] (
  .cons [(.mul archiveGenerator2 archiveGenerator103),
      (.mul archiveGenerator0 archiveGenerator115)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator101)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator107))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator113))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator112))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator110),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator111))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator110))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows81 : BasisRows generators 81 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator70)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator94))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator6 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator68))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator68)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator107))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator118,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator107)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator23)),
      (.mul archiveGenerator8 archiveGenerator64)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator32))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator13)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator63),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator112)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator20)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator40)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator39))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator117] (
  .cons [archiveGenerator116] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator111)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows82 : BasisRows generators 82 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator69)] (
  .cons [archiveGenerator122] (
  .cons [archiveGenerator121] (
  .cons [archiveGenerator120,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator6 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator68)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator68)] (
  .cons [(.mul archiveGenerator7 archiveGenerator72)] (
  .cons [(.mul archiveGenerator2 archiveGenerator114)] (
  .cons [archiveGenerator119] (
  .cons [(.mul archiveGenerator0 archiveGenerator118)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator64))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator117)] (
  .cons [(.mul archiveGenerator0 archiveGenerator116)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator110))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator111))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows83 : BasisRows generators 83 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator70)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator69))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator76)),
      (.mul archiveGenerator0 archiveGenerator122)] (
  .cons [(.mul archiveGenerator4 archiveGenerator92),
      (.mul archiveGenerator0 archiveGenerator121)] (
  .cons [(.mul archiveGenerator0 archiveGenerator120)] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator68))] (
  .cons [archiveGenerator124,
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator72))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator118))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator64)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator90)))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator117))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator116))] (
  .cons [archiveGenerator123] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator111)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows84 : BasisRows generators 84 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator69))] (
  .cons [archiveGenerator132,
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator69)))] (
  .cons [archiveGenerator131] (
  .cons [archiveGenerator130,
      (.mul archiveGenerator1 (.mul archiveGenerator8 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator69)))))] (
  .cons [archiveGenerator129,
      archiveGenerator128,
      (.mul archiveGenerator1 archiveGenerator122),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator121),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator122))] (
  .cons [(.mul archiveGenerator3 archiveGenerator107),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator121))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator120))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator68)))] (
  .cons [archiveGenerator127,
      archiveGenerator126,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator24))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)),
      (.mul archiveGenerator8 archiveGenerator72),
      (.mul archiveGenerator1 archiveGenerator119)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator32))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator42))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator23))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16)))] (
  .cons [archiveGenerator125,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator50)] (
  .cons [(.mul archiveGenerator16 archiveGenerator50)] (
  .cons [(.mul archiveGenerator8 archiveGenerator71)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator116)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows85 : BasisRows generators 85 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator69),
      (.mul archiveGenerator0 archiveGenerator132)] (
  .cons [(.mul archiveGenerator0 archiveGenerator131)] (
  .cons [(.mul archiveGenerator0 archiveGenerator130),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator69))))))] (
  .cons [archiveGenerator134,
      (.mul archiveGenerator0 archiveGenerator129),
      (.mul archiveGenerator0 archiveGenerator128)] (
  .cons [archiveGenerator133,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator122)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator107))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator120)))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator124)] (
  .cons [(.mul archiveGenerator0 archiveGenerator127),
      (.mul archiveGenerator0 archiveGenerator126)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator72))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator50))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator50))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator71))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator123)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows86 : BasisRows generators 86 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator11 archiveGenerator69)] (
  .cons [(.mul archiveGenerator10 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator132))] (
  .cons [(.mul archiveGenerator2 archiveGenerator122),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator8 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator122)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator130)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator69)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator129)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator128))] (
  .cons [(.mul archiveGenerator0 archiveGenerator133)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator107)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator120))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator127)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator126))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator72)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator125)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator71)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator135] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows87 : BasisRows generators 87 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator10 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator12 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator122))] (
  .cons [archiveGenerator139,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator69))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator128)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator8 archiveGenerator80)] (
  .cons [(.mul archiveGenerator8 archiveGenerator79)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator32))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13)))] (
  .cons [archiveGenerator138,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator46))] (
  .cons [archiveGenerator137,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator45))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19)))] (
  .cons [archiveGenerator136] (
  .cons [(.mul archiveGenerator17 archiveGenerator56)] (
  .cons [(.mul archiveGenerator8 archiveGenerator78)] (
  .cons [(.mul archiveGenerator8 archiveGenerator77),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator50))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows88 : BasisRows generators 88 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator143] (
  .cons [archiveGenerator142,
      (.mul archiveGenerator2 (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator69),
      (.mul archiveGenerator2 archiveGenerator132)] (
  .cons [(.mul archiveGenerator7 archiveGenerator92),
      (.mul archiveGenerator2 archiveGenerator131)] (
  .cons [(.mul archiveGenerator2 archiveGenerator130)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator122)))] (
  .cons [archiveGenerator141,
      (.mul archiveGenerator9 archiveGenerator75)] (
  .cons [(.mul archiveGenerator13 archiveGenerator67),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator128))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator126),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator80))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator79))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator138)] (
  .cons [(.mul archiveGenerator0 archiveGenerator137)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator56))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator78))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator77)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator50)))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator140] (
  .cons [(.mul archiveGenerator1 archiveGenerator135)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows89 : BasisRows generators 89 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator143)] (
  .cons [(.mul archiveGenerator0 archiveGenerator142)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator92)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator131))] (
  .cons [(.mul archiveGenerator7 archiveGenerator95)] (
  .cons [(.mul archiveGenerator2 archiveGenerator134),
      (.mul archiveGenerator1 (.mul archiveGenerator12 archiveGenerator69))] (
  .cons [(.mul archiveGenerator1 archiveGenerator139)] (
  .cons [(.mul archiveGenerator0 archiveGenerator141)] (
  .cons [archiveGenerator144,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator128)))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator80)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator79)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator137),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator138))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator137))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator78)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator77))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator50))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator140)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows90 : BasisRows generators 90 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator143)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator11 archiveGenerator69)),
      (.mul archiveGenerator1 archiveGenerator142),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator143))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator13 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator142))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator92)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator121),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator92)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator120)] (
  .cons [(.mul archiveGenerator14 archiveGenerator69)] (
  .cons [(.mul archiveGenerator1 archiveGenerator141)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator141))] (
  .cons [(.mul archiveGenerator9 archiveGenerator80),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator128))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator33)),
      (.mul archiveGenerator8 archiveGenerator89)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))] (
  .cons [archiveGenerator147,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator51))] (
  .cons [archiveGenerator146,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator23)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator22)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator8)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator138)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator88),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator137)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator17))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))))))))))))] (
  .cons [archiveGenerator145] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator140))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows91 : BasisRows generators 91 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator4 (.mul archiveGenerator7 archiveGenerator69))] (
  .cons [archiveGenerator148,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator143)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator142)))] (
  .cons [] (
  .cons [(.mul archiveGenerator13 archiveGenerator76)] (
  .cons [(.mul archiveGenerator13 archiveGenerator75),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator120))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator144),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator141)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator80)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator128)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator89))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator147)] (
  .cons [(.mul archiveGenerator0 archiveGenerator146)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator137))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator137))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator145)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows92 : BasisRows generators 92 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator143))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator13 archiveGenerator69)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator142))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator143))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator142))))] (
  .cons [] (
  .cons [(.mul archiveGenerator15 archiveGenerator69)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator14 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator75))] (
  .cons [archiveGenerator151] (
  .cons [archiveGenerator150] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator80)))] (
  .cons [archiveGenerator149] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator147))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator146))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator138)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator137)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator145),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator145))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows93 : BasisRows generators 93 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator4 (.mul archiveGenerator7 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator148),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator13 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator143)))))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator95))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator13 archiveGenerator76))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator15 archiveGenerator69))] (
  .cons [archiveGenerator155] (
  .cons [(.mul archiveGenerator13 archiveGenerator80)] (
  .cons [(.mul archiveGenerator8 archiveGenerator101)] (
  .cons [] (
  .cons [archiveGenerator154,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))] (
  .cons [(.mul archiveGenerator17 archiveGenerator64),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator51)),
      (.mul archiveGenerator0 archiveGenerator149)] (
  .cons [(.mul archiveGenerator16 archiveGenerator64),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator23)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator29)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator9))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator100),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator146)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator40))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator56)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator138))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator55)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator137))))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator153] (
  .cons [archiveGenerator152] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows94 : BasisRows generators 94 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator158] (
  .cons [(.mul archiveGenerator17 archiveGenerator69)] (
  .cons [(.mul archiveGenerator16 archiveGenerator69)] (
  .cons [archiveGenerator157] (
  .cons [(.mul archiveGenerator9 archiveGenerator95)] (
  .cons [(.mul archiveGenerator13 archiveGenerator83),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator15 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator155)] (
  .cons [archiveGenerator156,
      (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator80))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator101))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator149),
      (.mul archiveGenerator0 archiveGenerator154)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator64)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator149))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator64))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator138)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator137)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator153)] (
  .cons [(.mul archiveGenerator0 archiveGenerator152)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator145))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69))))))))))))))))))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows95 : BasisRows generators 95 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator69))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator80)))] (
  .cons [archiveGenerator160] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator154))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator64))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator149)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator64)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator138))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator137))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator153))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator152))] (
  .cons [archiveGenerator159] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator69)))))))))))))))))))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows96 : BasisRows generators 96 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator69))] (
  .cons [archiveGenerator163] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator2 (.mul archiveGenerator13 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator68)),
      (.mul archiveGenerator1 archiveGenerator158)] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator67))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator16 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator157),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator69)))] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator151)] (
  .cons [(.mul archiveGenerator9 archiveGenerator101),
      (.mul archiveGenerator2 archiveGenerator150)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator24)),
      (.mul archiveGenerator1 archiveGenerator156)] (
  .cons [archiveGenerator162,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator113),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator51)),
      (.mul archiveGenerator0 archiveGenerator160)] (
  .cons [(.mul archiveGenerator8 archiveGenerator112),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator23))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator32))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator154)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator13)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator149))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator60))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator17)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31)))] (
  .cons [archiveGenerator161] (
  .cons [] (
  .cons [(.mul archiveGenerator8 archiveGenerator111)] (
  .cons [(.mul archiveGenerator8 archiveGenerator110)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator152)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows97 : BasisRows generators 97 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator163)] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator70))] (
  .cons [] (
  .cons [(.mul archiveGenerator20 archiveGenerator69)] (
  .cons [(.mul archiveGenerator19 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator68)))] (
  .cons [archiveGenerator164] (
  .cons [(.mul archiveGenerator13 archiveGenerator95),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator69))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator162)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator113)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator160))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator112))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator154))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator149)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator111))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator110))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator159)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows98 : BasisRows generators 98 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator163),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator163))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator20 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator19 archiveGenerator69))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator16 archiveGenerator69)))] (
  .cons [archiveGenerator170,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator69)))))] (
  .cons [archiveGenerator169] (
  .cons [archiveGenerator168] (
  .cons [archiveGenerator167] (
  .cons [archiveGenerator166] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator113))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator160)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator112)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator154)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator149))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator161)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator110)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator165] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows99 : BasisRows generators 99 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator69)))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator70))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator163)))] (
  .cons [archiveGenerator174] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator20 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator19 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator21 archiveGenerator69)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator69))))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator101),
      (.mul archiveGenerator0 archiveGenerator169)] (
  .cons [archiveGenerator173,
      archiveGenerator172] (
  .cons [(.mul archiveGenerator17 archiveGenerator80),
      (.mul archiveGenerator0 archiveGenerator167)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator51)),
      (.mul archiveGenerator8 archiveGenerator118),
      (.mul archiveGenerator0 archiveGenerator166)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator23))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator32)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator13))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator63))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator20)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator40)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator39)))] (
  .cons [archiveGenerator171] (
  .cons [(.mul archiveGenerator17 archiveGenerator78)] (
  .cons [(.mul archiveGenerator8 archiveGenerator117)] (
  .cons [(.mul archiveGenerator8 archiveGenerator116)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows100 : BasisRows generators 100 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator25 archiveGenerator69),
      (.mul archiveGenerator2 archiveGenerator163)] (
  .cons [(.mul archiveGenerator24 archiveGenerator69),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator163))] (
  .cons [(.mul archiveGenerator23 archiveGenerator69)] (
  .cons [(.mul archiveGenerator22 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator163))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator69)),
      (.mul archiveGenerator0 archiveGenerator174)] (
  .cons [archiveGenerator179] (
  .cons [archiveGenerator178] (
  .cons [archiveGenerator177,
      (.mul archiveGenerator13 archiveGenerator107),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator19 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator105),
      (.mul archiveGenerator1 archiveGenerator170)] (
  .cons [archiveGenerator176,
      (.mul archiveGenerator1 archiveGenerator169)] (
  .cons [(.mul archiveGenerator1 archiveGenerator168),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator169))] (
  .cons [(.mul archiveGenerator0 archiveGenerator172)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator80)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator167))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator118)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator166))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator78))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator117))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator116))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator175] (
  .cons [(.mul archiveGenerator1 archiveGenerator165)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows101 : BasisRows generators 101 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator26 archiveGenerator69)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator163))] (
  .cons [] (
  .cons [archiveGenerator181,
      (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator69))] (
  .cons [(.mul archiveGenerator1 archiveGenerator174),
      (.mul archiveGenerator0 (.mul archiveGenerator22 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator163)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator179)] (
  .cons [(.mul archiveGenerator0 archiveGenerator178)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator21 archiveGenerator69)),
      (.mul archiveGenerator0 archiveGenerator177)] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator176)] (
  .cons [archiveGenerator180,
      (.mul archiveGenerator1 archiveGenerator172),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator169)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator172))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator167)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator118)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator137)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator117)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator116)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator175)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows102 : BasisRows generators 102 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator26 archiveGenerator69))] (
  .cons [archiveGenerator191,
      (.mul archiveGenerator28 archiveGenerator69)] (
  .cons [archiveGenerator190] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator69)))] (
  .cons [archiveGenerator189,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator22 archiveGenerator69)))] (
  .cons [archiveGenerator188,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator69))))] (
  .cons [archiveGenerator187] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator178))] (
  .cons [(.mul archiveGenerator27 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator177))] (
  .cons [archiveGenerator186,
      (.mul archiveGenerator1 archiveGenerator176)] (
  .cons [(.mul archiveGenerator20 archiveGenerator80),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator52)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator176))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)),
      (.mul archiveGenerator8 archiveGenerator127),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator169))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator72)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator172)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator32))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator167))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13))))] (
  .cons [archiveGenerator185,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator42)))] (
  .cons [archiveGenerator184,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator23)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator125)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator50))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator183] (
  .cons [archiveGenerator182] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator175))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows103 : BasisRows generators 103 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator29 archiveGenerator69),
      (.mul archiveGenerator0 archiveGenerator191)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator69)),
      (.mul archiveGenerator1 archiveGenerator181),
      (.mul archiveGenerator0 archiveGenerator190)] (
  .cons [archiveGenerator192,
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator174)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator23 archiveGenerator76),
      (.mul archiveGenerator0 archiveGenerator189)] (
  .cons [(.mul archiveGenerator23 archiveGenerator75),
      (.mul archiveGenerator0 archiveGenerator188)] (
  .cons [(.mul archiveGenerator0 archiveGenerator187)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator20 archiveGenerator80)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator176)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator127)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator169)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator72))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator172))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator167)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator185)] (
  .cons [(.mul archiveGenerator0 archiveGenerator184)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator137))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator183)] (
  .cons [(.mul archiveGenerator0 archiveGenerator182)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows104 : BasisRows generators 104 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator7 archiveGenerator143)] (
  .cons [(.mul archiveGenerator3 archiveGenerator163)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator25 archiveGenerator69))] (
  .cons [archiveGenerator198,
      (.mul archiveGenerator2 (.mul archiveGenerator24 archiveGenerator69))] (
  .cons [archiveGenerator197,
      (.mul archiveGenerator1 (.mul archiveGenerator28 archiveGenerator69))] (
  .cons [(.mul archiveGenerator1 archiveGenerator190),
      (.mul archiveGenerator0 (.mul archiveGenerator29 archiveGenerator69))] (
  .cons [archiveGenerator196,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator190))] (
  .cons [(.mul archiveGenerator1 archiveGenerator189),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator69)))))] (
  .cons [archiveGenerator195,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator189))] (
  .cons [(.mul archiveGenerator1 archiveGenerator187),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator188))] (
  .cons [(.mul archiveGenerator30 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator187))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator27 archiveGenerator69))] (
  .cons [archiveGenerator194] (
  .cons [archiveGenerator193] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator127)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator172)))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator185))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator184))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator182),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator183))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator182))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows105 : BasisRows generators 105 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator143))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator163))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator198)] (
  .cons [(.mul archiveGenerator2 archiveGenerator181),
      (.mul archiveGenerator0 archiveGenerator197)] (
  .cons [archiveGenerator202,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator29 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator192),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator69))))] (
  .cons [archiveGenerator201,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator69))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator195)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator188)))] (
  .cons [(.mul archiveGenerator23 archiveGenerator80),
      (.mul archiveGenerator0 (.mul archiveGenerator30 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator187)))] (
  .cons [(.mul archiveGenerator22 archiveGenerator80)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator79))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator32)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator138),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator46)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator137),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator45)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator136),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator184)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator56))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator78))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator77))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator200] (
  .cons [archiveGenerator199] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator183)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows106 : BasisRows generators 106 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator35 archiveGenerator69)] (
  .cons [(.mul archiveGenerator34 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator143)))] (
  .cons [archiveGenerator204,
      archiveGenerator203,
      (.mul archiveGenerator33 archiveGenerator69)] (
  .cons [(.mul archiveGenerator32 archiveGenerator69),
      (.mul archiveGenerator2 archiveGenerator191)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator198))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator197))] (
  .cons [(.mul archiveGenerator2 archiveGenerator189),
      (.mul archiveGenerator0 archiveGenerator202)] (
  .cons [(.mul archiveGenerator2 archiveGenerator188),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator189))] (
  .cons [(.mul archiveGenerator31 archiveGenerator69),
      (.mul archiveGenerator9 archiveGenerator133),
      (.mul archiveGenerator1 archiveGenerator195),
      (.mul archiveGenerator0 archiveGenerator201)] (
  .cons [(.mul archiveGenerator23 archiveGenerator83),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator187)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator195))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator188))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator30 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator187))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator193),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator79)))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator149)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator138))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator137))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator200)] (
  .cons [(.mul archiveGenerator0 archiveGenerator199)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator182))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator183))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows107 : BasisRows generators 107 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator34 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 archiveGenerator203)] (
  .cons [(.mul archiveGenerator3 archiveGenerator174),
      (.mul archiveGenerator0 (.mul archiveGenerator32 archiveGenerator69))] (
  .cons [archiveGenerator209,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator69)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator188))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator31 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator201))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator188)))))] (
  .cons [archiveGenerator208,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator187)))))] (
  .cons [archiveGenerator207] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80))))] (
  .cons [archiveGenerator206] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator138)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator137)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator200))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator199))] (
  .cons [archiveGenerator205] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator183)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows108 : BasisRows generators 108 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator38 archiveGenerator69)] (
  .cons [(.mul archiveGenerator37 archiveGenerator69)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator35 archiveGenerator69))] (
  .cons [archiveGenerator214,
      (.mul archiveGenerator36 archiveGenerator69),
      (.mul archiveGenerator1 (.mul archiveGenerator34 archiveGenerator69))] (
  .cons [(.mul archiveGenerator2 archiveGenerator198),
      (.mul archiveGenerator1 archiveGenerator203),
      (.mul archiveGenerator1 (.mul archiveGenerator33 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator34 archiveGenerator69)))] (
  .cons [archiveGenerator213,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator203))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator174)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator32 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator209),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator69))))] (
  .cons [archiveGenerator212,
      (.mul archiveGenerator3 archiveGenerator178)] (
  .cons [(.mul archiveGenerator2 archiveGenerator195)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator31 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator31 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator201)))] (
  .cons [(.mul archiveGenerator23 archiveGenerator89)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator24))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator80)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator188))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator89)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator187))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))),
      (.mul archiveGenerator0 archiveGenerator207)] (
  .cons [(.mul archiveGenerator17 archiveGenerator113),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator147),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator51))),
      (.mul archiveGenerator0 archiveGenerator206)] (
  .cons [(.mul archiveGenerator8 archiveGenerator146),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator23)))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator22))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator8)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator88))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator17)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49)))] (
  .cons [archiveGenerator211,
      archiveGenerator210] (
  .cons [(.mul archiveGenerator17 archiveGenerator111)] (
  .cons [(.mul archiveGenerator16 archiveGenerator111)] (
  .cons [(.mul archiveGenerator8 archiveGenerator145)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator199)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows109 : BasisRows generators 109 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator38 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator37 archiveGenerator69))] (
  .cons [] (
  .cons [archiveGenerator216,
      (.mul archiveGenerator0 (.mul archiveGenerator36 archiveGenerator69))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator69)),
      (.mul archiveGenerator3 archiveGenerator181),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator34 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator181)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator203)))] (
  .cons [(.mul archiveGenerator2 archiveGenerator202),
      (.mul archiveGenerator1 archiveGenerator209)] (
  .cons [(.mul archiveGenerator40 archiveGenerator69),
      (.mul archiveGenerator13 archiveGenerator134),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator209))] (
  .cons [(.mul archiveGenerator39 archiveGenerator69),
      (.mul archiveGenerator13 archiveGenerator133),
      (.mul archiveGenerator0 archiveGenerator212)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator195))] (
  .cons [archiveGenerator215] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator188)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator187)))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator113))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator147)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator206))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator146))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator210)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator111))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator111))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator145))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator205)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows110 : BasisRows generators 110 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator38 archiveGenerator69)))] (
  .cons [archiveGenerator222,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator37 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator191),
      (.mul archiveGenerator1 archiveGenerator214),
      (.mul archiveGenerator1 (.mul archiveGenerator36 archiveGenerator69))] (
  .cons [(.mul archiveGenerator3 archiveGenerator190),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator203)),
      (.mul archiveGenerator0 archiveGenerator216),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator36 archiveGenerator69)))] (
  .cons [archiveGenerator221,
      (.mul archiveGenerator1 archiveGenerator213),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator34 archiveGenerator69)))))] (
  .cons [(.mul archiveGenerator3 archiveGenerator189)] (
  .cons [(.mul archiveGenerator3 archiveGenerator188),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator189))] (
  .cons [(.mul archiveGenerator1 archiveGenerator212),
      (.mul archiveGenerator0 (.mul archiveGenerator40 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator209)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator39 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator212))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator31 archiveGenerator69)))] (
  .cons [archiveGenerator220] (
  .cons [archiveGenerator219] (
  .cons [archiveGenerator218] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator188))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator149)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator147))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator206)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator146)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator210)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator145)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator217] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows111 : BasisRows generators 111 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator191))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator216)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator36 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator2 archiveGenerator209),
      (.mul archiveGenerator0 archiveGenerator221),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator34 archiveGenerator69))))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator189))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator188))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator40 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator209))))] (
  .cons [archiveGenerator226,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator39 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator41 archiveGenerator69),
      (.mul archiveGenerator23 archiveGenerator101),
      (.mul archiveGenerator1 archiveGenerator215)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator80))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator101))] (
  .cons [(.mul archiveGenerator42 archiveGenerator64),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator154),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator51))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator23))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator29))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator9)))))] (
  .cons [archiveGenerator225,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator100))] (
  .cons [archiveGenerator224,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator40)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator56)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator55)))] (
  .cons [archiveGenerator223] (
  .cons [(.mul archiveGenerator17 archiveGenerator117)] (
  .cons [(.mul archiveGenerator8 archiveGenerator153)] (
  .cons [(.mul archiveGenerator8 archiveGenerator152),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator111))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows112 : BasisRows generators 112 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator7 archiveGenerator163)] (
  .cons [archiveGenerator231] (
  .cons [archiveGenerator230] (
  .cons [(.mul archiveGenerator3 archiveGenerator198)] (
  .cons [(.mul archiveGenerator3 archiveGenerator197)] (
  .cons [(.mul archiveGenerator43 archiveGenerator68),
      (.mul archiveGenerator42 archiveGenerator69),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator190))] (
  .cons [archiveGenerator229,
      (.mul archiveGenerator43 archiveGenerator67),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator216)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator69)),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator189)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator221))] (
  .cons [(.mul archiveGenerator3 archiveGenerator195),
      (.mul archiveGenerator2 archiveGenerator212),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator189)))] (
  .cons [archiveGenerator228,
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator75)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator188)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator67)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator209)))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator226)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator154))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator149)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator225)] (
  .cons [(.mul archiveGenerator0 archiveGenerator224)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator117))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator153))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator152)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator111)))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator227] (
  .cons [(.mul archiveGenerator1 archiveGenerator217)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows113 : BasisRows generators 113 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator163))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator230)] (
  .cons [archiveGenerator235,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator198))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator197))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator68))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator67))] (
  .cons [archiveGenerator234,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator221)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator195)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator212))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator188))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator209))))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator41 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator226))] (
  .cons [archiveGenerator233] (
  .cons [archiveGenerator232] (
  .cons [(.mul archiveGenerator8 archiveGenerator160),
      (.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator64))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator224),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator225))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator224))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator153)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator152))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator111))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator227)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows114 : BasisRows generators 114 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator242] (
  .cons [archiveGenerator241,
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator163))] (
  .cons [archiveGenerator240,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator163)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator203)] (
  .cons [archiveGenerator239] (
  .cons [(.mul archiveGenerator0 archiveGenerator235)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator68)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator67)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator195)))] (
  .cons [] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator80))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator33))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator101))] (
  .cons [(.mul archiveGenerator23 archiveGenerator113),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator162),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator113)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator51)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator112)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator23))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator32))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator13)))))] (
  .cons [archiveGenerator238,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator60)))] (
  .cons [archiveGenerator237,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator17))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator225)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator161),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator224)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator50))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator111))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator110))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210))))))] (
  .cons [archiveGenerator236] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator227))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows115 : BasisRows generators 115 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator241)] (
  .cons [(.mul archiveGenerator0 archiveGenerator240)] (
  .cons [(.mul archiveGenerator43 archiveGenerator76),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator203))] (
  .cons [(.mul archiveGenerator43 archiveGenerator74),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator174)),
      (.mul archiveGenerator0 archiveGenerator239)] (
  .cons [(.mul archiveGenerator3 archiveGenerator209),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator235))] (
  .cons [archiveGenerator243,
      (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator69))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator76)),
      (.mul archiveGenerator8 (.mul archiveGenerator19 archiveGenerator69))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator75))] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator226)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator162))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator113)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator112)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator238)] (
  .cons [(.mul archiveGenerator0 archiveGenerator237)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator224))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator225))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator224))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator110)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210)))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator236)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows116 : BasisRows generators 116 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator38 archiveGenerator69))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator163))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator251] (
  .cons [(.mul archiveGenerator3 archiveGenerator213),
      (.mul archiveGenerator1 archiveGenerator239)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator74)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator174)))] (
  .cons [archiveGenerator250,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator235)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator69)))] (
  .cons [archiveGenerator249,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator19 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator2 archiveGenerator228)] (
  .cons [(.mul archiveGenerator13 archiveGenerator151)] (
  .cons [(.mul archiveGenerator13 archiveGenerator150),
      (.mul archiveGenerator5 archiveGenerator187)] (
  .cons [archiveGenerator248] (
  .cons [(.mul archiveGenerator8 archiveGenerator167)] (
  .cons [(.mul archiveGenerator8 archiveGenerator166)] (
  .cons [archiveGenerator247,
      archiveGenerator246] (
  .cons [archiveGenerator245] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator113))))] (
  .cons [archiveGenerator244] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator238))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator237))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator225)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator224)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator111))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator110))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator236),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator236))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows117 : BasisRows generators 117 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator163)))] (
  .cons [(.mul archiveGenerator48 archiveGenerator69)] (
  .cons [(.mul archiveGenerator3 archiveGenerator216)] (
  .cons [(.mul archiveGenerator0 archiveGenerator251)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator250),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator235))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator69))))] (
  .cons [archiveGenerator255] (
  .cons [archiveGenerator254] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator101))] (
  .cons [(.mul archiveGenerator8 archiveGenerator173)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))),
      (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator80))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator51))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator118))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator23)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64))),
      (.mul archiveGenerator0 archiveGenerator246)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator32)))),
      (.mul archiveGenerator0 archiveGenerator245)] (
  .cons [(.mul archiveGenerator17 archiveGenerator138),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator13)))))] (
  .cons [(.mul archiveGenerator16 archiveGenerator138),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator63))),
      (.mul archiveGenerator0 archiveGenerator244)] (
  .cons [(.mul archiveGenerator16 archiveGenerator137),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator20))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator40))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator39))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator171),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator237)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator78))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator117)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator225))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator116)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator224))))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator253] (
  .cons [archiveGenerator252] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210)))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows118 : BasisRows generators 118 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator3 archiveGenerator222)] (
  .cons [(.mul archiveGenerator7 archiveGenerator190),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator191))] (
  .cons [(.mul archiveGenerator1 archiveGenerator251),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator216))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator213)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator239)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator251))] (
  .cons [(.mul archiveGenerator7 archiveGenerator188),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator189))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator188)),
      (.mul archiveGenerator1 archiveGenerator250)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator235)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator95)),
      (.mul archiveGenerator1 archiveGenerator249)] (
  .cons [(.mul archiveGenerator50 archiveGenerator69),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator83)),
      (.mul archiveGenerator0 archiveGenerator255)] (
  .cons [(.mul archiveGenerator49 archiveGenerator69),
      (.mul archiveGenerator0 archiveGenerator254)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator187))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator246),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator118)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245))] (
  .cons [(.mul archiveGenerator1 archiveGenerator244),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator138))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator138)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator244))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator137))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator225)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator224)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator253)] (
  .cons [(.mul archiveGenerator0 archiveGenerator252)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator236))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows119 : BasisRows generators 119 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator264] (
  .cons [(.mul archiveGenerator53 archiveGenerator69)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator48 archiveGenerator69))] (
  .cons [archiveGenerator263,
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator191)))] (
  .cons [archiveGenerator262,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator216)))] (
  .cons [archiveGenerator261] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator188))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator188)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator50 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator255))] (
  .cons [archiveGenerator260,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator254))] (
  .cons [(.mul archiveGenerator9 archiveGenerator167)] (
  .cons [(.mul archiveGenerator8 archiveGenerator180)] (
  .cons [archiveGenerator259] (
  .cons [archiveGenerator258] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator118))))] (
  .cons [archiveGenerator257,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator138)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator138))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator244)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator137)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator225))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator224))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator253))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator252))] (
  .cons [archiveGenerator256] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator210)))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows120 : BasisRows generators 120 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator273] (
  .cons [(.mul archiveGenerator54 archiveGenerator69),
      (.mul archiveGenerator3 archiveGenerator231)] (
  .cons [archiveGenerator272,
      (.mul archiveGenerator3 archiveGenerator230),
      (.mul archiveGenerator0 archiveGenerator264)] (
  .cons [archiveGenerator271,
      archiveGenerator270,
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator198)),
      (.mul archiveGenerator0 (.mul archiveGenerator53 archiveGenerator69))] (
  .cons [archiveGenerator269,
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator197)),
      (.mul archiveGenerator2 archiveGenerator251)] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator268] (
  .cons [archiveGenerator267,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator188)))] (
  .cons [archiveGenerator266,
      (.mul archiveGenerator8 archiveGenerator188)] (
  .cons [(.mul archiveGenerator8 archiveGenerator187)] (
  .cons [] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator101)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator50 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator24))),
      (.mul archiveGenerator8 archiveGenerator186),
      (.mul archiveGenerator0 archiveGenerator260)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))),
      (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator80))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator127))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator72)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator32)))),
      (.mul archiveGenerator0 archiveGenerator258)] (
  .cons [(.mul archiveGenerator17 archiveGenerator147),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator185),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator42)))),
      (.mul archiveGenerator0 archiveGenerator257),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator184),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator23)))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator244)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator244))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator125))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71)))] (
  .cons [archiveGenerator265] (
  .cons [] (
  .cons [(.mul archiveGenerator8 archiveGenerator183)] (
  .cons [(.mul archiveGenerator8 archiveGenerator182)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator252)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows121 : BasisRows generators 121 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator57 archiveGenerator69)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator270),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator53 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator197))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator251))] (
  .cons [archiveGenerator275,
      (.mul archiveGenerator8 (.mul archiveGenerator29 archiveGenerator69))] (
  .cons [(.mul archiveGenerator1 archiveGenerator261)] (
  .cons [(.mul archiveGenerator13 archiveGenerator164)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator95)),
      (.mul archiveGenerator5 archiveGenerator209),
      (.mul archiveGenerator0 archiveGenerator267)] (
  .cons [(.mul archiveGenerator56 archiveGenerator69),
      (.mul archiveGenerator0 archiveGenerator266),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator188))] (
  .cons [(.mul archiveGenerator55 archiveGenerator69),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator187))] (
  .cons [] (
  .cons [archiveGenerator274,
      (.mul archiveGenerator1 archiveGenerator260)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator260))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator147))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator185)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator257)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator184)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator138)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator244)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator183))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator182))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator256)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows122 : BasisRows generators 122 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator282] (
  .cons [archiveGenerator281,
      (.mul archiveGenerator1 archiveGenerator270)] (
  .cons [(.mul archiveGenerator1 archiveGenerator269),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator270))] (
  .cons [] (
  .cons [archiveGenerator280] (
  .cons [archiveGenerator279] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator267))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator56 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator266)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator188)))] (
  .cons [archiveGenerator278,
      (.mul archiveGenerator13 archiveGenerator168),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator187)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator167)] (
  .cons [(.mul archiveGenerator8 archiveGenerator194),
      (.mul archiveGenerator0 archiveGenerator274)] (
  .cons [(.mul archiveGenerator8 archiveGenerator193),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator260)))] (
  .cons [archiveGenerator277] (
  .cons [(.mul archiveGenerator17 archiveGenerator149)] (
  .cons [(.mul archiveGenerator16 archiveGenerator149)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator185))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator257))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator184))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator138))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator244))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator265)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator183)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator182)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator276] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows123 : BasisRows generators 123 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator264)] (
  .cons [archiveGenerator289,
      (.mul archiveGenerator2 (.mul archiveGenerator53 archiveGenerator69))] (
  .cons [archiveGenerator288] (
  .cons [(.mul archiveGenerator7 archiveGenerator209),
      (.mul archiveGenerator0 archiveGenerator281)] (
  .cons [(.mul archiveGenerator2 archiveGenerator262),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator270)))] (
  .cons [archiveGenerator287,
      (.mul archiveGenerator1 archiveGenerator275)] (
  .cons [archiveGenerator286,
      archiveGenerator285] (
  .cons [archiveGenerator284,
      (.mul archiveGenerator9 archiveGenerator188)] (
  .cons [(.mul archiveGenerator8 archiveGenerator201),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator209))] (
  .cons [] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator56 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator80)),
      (.mul archiveGenerator0 archiveGenerator278)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator80)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator260))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator274))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator79))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator59 archiveGenerator64),
      (.mul archiveGenerator17 archiveGenerator154),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator32))))] (
  .cons [(.mul archiveGenerator16 archiveGenerator154),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator46)))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator45))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator136)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator56)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator78)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator77)))] (
  .cons [archiveGenerator283] (
  .cons [(.mul archiveGenerator17 archiveGenerator153)] (
  .cons [(.mul archiveGenerator8 archiveGenerator200)] (
  .cons [(.mul archiveGenerator8 archiveGenerator199)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows124 : BasisRows generators 124 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator273)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator54 archiveGenerator69))] (
  .cons [(.mul archiveGenerator2 archiveGenerator272)] (
  .cons [(.mul archiveGenerator2 archiveGenerator270),
      (.mul archiveGenerator1 archiveGenerator282)] (
  .cons [(.mul archiveGenerator1 archiveGenerator281),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator270))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator209))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator270))))] (
  .cons [(.mul archiveGenerator59 archiveGenerator69),
      (.mul archiveGenerator2 archiveGenerator268),
      (.mul archiveGenerator1 archiveGenerator280)] (
  .cons [(.mul archiveGenerator1 archiveGenerator279),
      (.mul archiveGenerator0 archiveGenerator286),
      (.mul archiveGenerator0 archiveGenerator285)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator75)),
      (.mul archiveGenerator0 archiveGenerator284),
      (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator188))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator105)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator201))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator278)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator278))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator274)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator260)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator154))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator154)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator149)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator149)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137)))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator153))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator200))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator199))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator290] (
  .cons [(.mul archiveGenerator1 archiveGenerator276)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows125 : BasisRows generators 125 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator289)] (
  .cons [] (
  .cons [(.mul archiveGenerator13 archiveGenerator181)] (
  .cons [archiveGenerator294,
      (.mul archiveGenerator2 archiveGenerator275)] (
  .cons [(.mul archiveGenerator8 archiveGenerator209),
      (.mul archiveGenerator1 archiveGenerator287)] (
  .cons [archiveGenerator293,
      (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator69))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator285))] (
  .cons [archiveGenerator292,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator284)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator188)))] (
  .cons [archiveGenerator291,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator201)))] (
  .cons [] (
  .cons [(.mul archiveGenerator9 archiveGenerator194)] (
  .cons [(.mul archiveGenerator8 archiveGenerator208),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator278)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator207)] (
  .cons [(.mul archiveGenerator17 archiveGenerator160),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator274))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator206),
      (.mul archiveGenerator1 (.mul archiveGenerator59 archiveGenerator64)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator260))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator154)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator149))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))] (
  .cons [(.mul archiveGenerator5 archiveGenerator224),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245)))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator200)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator199)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator290)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows126 : BasisRows generators 126 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator310] (
  .cons [archiveGenerator309,
      (.mul archiveGenerator13 archiveGenerator190)] (
  .cons [archiveGenerator308,
      archiveGenerator307] (
  .cons [archiveGenerator306,
      (.mul archiveGenerator13 archiveGenerator189)] (
  .cons [archiveGenerator305,
      archiveGenerator304,
      (.mul archiveGenerator13 archiveGenerator188),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator209))] (
  .cons [archiveGenerator303,
      archiveGenerator302,
      (.mul archiveGenerator8 archiveGenerator212),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator69)))] (
  .cons [archiveGenerator301,
      archiveGenerator300] (
  .cons [(.mul archiveGenerator0 archiveGenerator292)] (
  .cons [archiveGenerator299,
      (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator80)),
      (.mul archiveGenerator0 archiveGenerator291)] (
  .cons [(.mul archiveGenerator64 archiveGenerator64),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator52))),
      (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator89))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator80)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator89)))] (
  .cons [(.mul archiveGenerator17 archiveGenerator162),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator113)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator274)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator147)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator51)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator260)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator146)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator23))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator154))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator22))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator149)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator8))))))] (
  .cons [archiveGenerator298,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator88)))] (
  .cons [archiveGenerator297,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator17))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245))))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator211)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator111))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator111))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator145))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator296] (
  .cons [archiveGenerator295] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator290))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows127 : BasisRows generators 127 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator314,
      archiveGenerator313] (
  .cons [archiveGenerator312,
      archiveGenerator311] (
  .cons [(.mul archiveGenerator64 archiveGenerator69)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator287),
      (.mul archiveGenerator0 archiveGenerator308)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator76)),
      (.mul archiveGenerator2 archiveGenerator286),
      (.mul archiveGenerator1 (.mul archiveGenerator8 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator306)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator75)),
      (.mul archiveGenerator1 archiveGenerator293),
      (.mul archiveGenerator0 archiveGenerator304),
      (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator188))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator301),
      (.mul archiveGenerator0 archiveGenerator300)] (
  .cons [(.mul archiveGenerator1 archiveGenerator291),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator292))] (
  .cons [(.mul archiveGenerator0 archiveGenerator299),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator291))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator64))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator113))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator274))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator147))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator260))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator146))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator154)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator149))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator298)] (
  .cons [(.mul archiveGenerator0 archiveGenerator297)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator224)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245)))))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator145)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator296)] (
  .cons [(.mul archiveGenerator0 archiveGenerator295)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end KIP126.Computation.StandardArchive
