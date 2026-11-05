module

import all KIP126.AdamsComputation.Internal.SphereArchive.Basic
import all KIP126.AdamsComputation.Internal.SphereArchive.Generators

/-! Ordered S⁰ basis monomials in internal degrees 192–223.
Standard supplies their Adams E₂ interpretation. -/

@[expose] section
namespace KIP126.Computation.StandardArchive
open KIP126.Computation
set_option backward.privateInPublic true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private noncomputable def archiveMonomialRows192 : BasisRows generators 192 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324))] (
  .cons [archiveGenerator1058] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator68 archiveGenerator324)] (
  .cons [(.mul archiveGenerator67 archiveGenerator324),
      (.mul archiveGenerator2 archiveGenerator994)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator617))] (
  .cons [] (
  .cons [(.mul archiveGenerator66 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator18 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1027),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1028))] (
  .cons [archiveGenerator1057,
      (.mul archiveGenerator1 archiveGenerator1026),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1027))] (
  .cons [archiveGenerator1056,
      archiveGenerator1055] (
  .cons [(.mul archiveGenerator2 archiveGenerator991),
      (.mul archiveGenerator2 archiveGenerator990),
      (.mul archiveGenerator1 archiveGenerator1023)] (
  .cons [archiveGenerator1054,
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator843)),
      (.mul archiveGenerator1 archiveGenerator1022),
      (.mul archiveGenerator1 (.mul archiveGenerator43 archiveGenerator485)),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator20 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1019),
      (.mul archiveGenerator0 archiveGenerator1046),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator40 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1021))] (
  .cons [archiveGenerator1053,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator39 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1017)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324)))))] (
  .cons [archiveGenerator1052,
      (.mul archiveGenerator1 archiveGenerator1014),
      (.mul archiveGenerator1 archiveGenerator1013),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1015)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator324))))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1011),
      (.mul archiveGenerator0 archiveGenerator1040),
      (.mul archiveGenerator0 archiveGenerator1039),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1014)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator987))))] (
  .cons [archiveGenerator1051,
      archiveGenerator1050,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1011))] (
  .cons [(.mul archiveGenerator65 archiveGenerator324),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator288))),
      (.mul archiveGenerator0 archiveGenerator1037)] (
  .cons [archiveGenerator1049,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator213))),
      (.mul archiveGenerator1 (.mul archiveGenerator62 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1036)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator188)),
      (.mul archiveGenerator7 archiveGenerator832),
      (.mul archiveGenerator3 archiveGenerator929)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator268))),
      (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator201)),
      (.mul archiveGenerator2 archiveGenerator978)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator267))),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator286))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator610)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator978))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator266))),
      (.mul archiveGenerator8 archiveGenerator813),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188)))),
      (.mul archiveGenerator2 archiveGenerator973),
      (.mul archiveGenerator0 archiveGenerator1035),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator318))] (
  .cons [(.mul archiveGenerator8 archiveGenerator812),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212)))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator655)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator963)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator978))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator327),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator188)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator797)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator976))))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator72)),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator267)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator301)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator974))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator24)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator188))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator963)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator187))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator299))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator435))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator434))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator1 archiveGenerator1009)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator299))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator186))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator898))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator64)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator80)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator919)))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator808),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator127))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator138)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator72))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator491)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator225)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator113))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator491)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator224)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator147))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator185))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator42))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator184))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator23))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator238))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17))))))))),
      (.mul archiveGenerator0 archiveGenerator1033)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator298))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator433))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator125))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator432))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator50)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50))))))),
      (.mul archiveGenerator0 archiveGenerator1031)] (
  .cons [(.mul archiveGenerator17 archiveGenerator663),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator806),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator265)))),
      (.mul archiveGenerator0 archiveGenerator1030)] (
  .cons [(.mul archiveGenerator8 archiveGenerator805),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator111))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator969))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator183))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator636))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator182))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator969))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator607))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator296)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator296)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator431)))] (
  .cons [archiveGenerator1048] (
  .cons [] (
  .cons [(.mul archiveGenerator8 archiveGenerator804)] (
  .cons [(.mul archiveGenerator8 archiveGenerator803)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator995)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows193 : BasisRows generators 193 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator70 archiveGenerator324),
      (.mul archiveGenerator0 archiveGenerator1058)] (
  .cons [(.mul archiveGenerator18 archiveGenerator660)] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator324))] (
  .cons [(.mul archiveGenerator18 (.mul archiveGenerator20 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator324))] (
  .cons [(.mul archiveGenerator18 archiveGenerator659),
      (.mul archiveGenerator18 (.mul archiveGenerator19 archiveGenerator324))] (
  .cons [(.mul archiveGenerator70 archiveGenerator323),
      (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator333))] (
  .cons [archiveGenerator1074,
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator66 archiveGenerator324))] (
  .cons [(.mul archiveGenerator7 archiveGenerator860),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324)))] (
  .cons [archiveGenerator1073,
      (.mul archiveGenerator2 archiveGenerator1008),
      (.mul archiveGenerator0 archiveGenerator1057)] (
  .cons [archiveGenerator1072,
      archiveGenerator1071,
      (.mul archiveGenerator1 archiveGenerator1047),
      (.mul archiveGenerator0 archiveGenerator1056),
      (.mul archiveGenerator0 archiveGenerator1055)] (
  .cons [archiveGenerator1070,
      archiveGenerator1069,
      (.mul archiveGenerator67 archiveGenerator333)] (
  .cons [(.mul archiveGenerator9 archiveGenerator787),
      (.mul archiveGenerator2 archiveGenerator1004),
      (.mul archiveGenerator1 archiveGenerator1046)] (
  .cons [archiveGenerator1068,
      archiveGenerator1067,
      (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator190)),
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator376)),
      (.mul archiveGenerator2 archiveGenerator1002),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator40 archiveGenerator324))))] (
  .cons [archiveGenerator1066,
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator373)),
      (.mul archiveGenerator1 archiveGenerator1043),
      (.mul archiveGenerator1 archiveGenerator1042),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator39 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324))))))] (
  .cons [archiveGenerator1065,
      archiveGenerator1064,
      (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator189)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1015))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator324)))))))] (
  .cons [(.mul archiveGenerator76 archiveGenerator302),
      (.mul archiveGenerator18 archiveGenerator655),
      (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator188)),
      (.mul archiveGenerator7 archiveGenerator857)] (
  .cons [(.mul archiveGenerator23 archiveGenerator618),
      (.mul archiveGenerator0 archiveGenerator1051),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1011)))] (
  .cons [archiveGenerator1063,
      archiveGenerator1062,
      (.mul archiveGenerator0 (.mul archiveGenerator65 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1049)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator929))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator164)))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator978))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator95)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator655))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator963))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator978)))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator784),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator797))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator976)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator821),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator301))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator974)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator820),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator963))))))] (
  .cons [archiveGenerator1061,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator299)))))] (
  .cons [archiveGenerator1060,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator491)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator898)))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator919))))))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator244)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator225))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator224)))] (
  .cons [] (
  .cons [archiveGenerator1059,
      (.mul archiveGenerator1 archiveGenerator1033)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1033))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator663))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator806)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1030))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator805))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator636)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator969)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator804))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator803))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1029)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows194 : BasisRows generators 194 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1058),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator341)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator660))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator20 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator72 archiveGenerator324),
      (.mul archiveGenerator13 (.mul archiveGenerator33 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator659))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator32 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator333)))] (
  .cons [archiveGenerator1091,
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator66 archiveGenerator324)))] (
  .cons [archiveGenerator1090,
      archiveGenerator1089,
      (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1057),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324))))] (
  .cons [archiveGenerator1088,
      (.mul archiveGenerator16 (.mul archiveGenerator23 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1055),
      (.mul archiveGenerator0 archiveGenerator1073),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1057))] (
  .cons [archiveGenerator1087,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator324))),
      (.mul archiveGenerator0 archiveGenerator1071),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1056)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1055))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator324))),
      (.mul archiveGenerator0 archiveGenerator1069),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator333))] (
  .cons [archiveGenerator1086,
      archiveGenerator1085,
      (.mul archiveGenerator67 archiveGenerator336),
      (.mul archiveGenerator8 archiveGenerator842)] (
  .cons [(.mul archiveGenerator8 archiveGenerator841),
      (.mul archiveGenerator0 archiveGenerator1068),
      (.mul archiveGenerator0 archiveGenerator1067),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1002))] (
  .cons [(.mul archiveGenerator3 archiveGenerator960),
      (.mul archiveGenerator1 archiveGenerator1052),
      (.mul archiveGenerator0 archiveGenerator1066),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324)))))))] (
  .cons [(.mul archiveGenerator71 archiveGenerator324),
      (.mul archiveGenerator64 archiveGenerator351),
      (.mul archiveGenerator24 archiveGenerator629),
      (.mul archiveGenerator3 archiveGenerator959),
      (.mul archiveGenerator0 archiveGenerator1064),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1015))))] (
  .cons [archiveGenerator1084,
      archiveGenerator1083,
      (.mul archiveGenerator23 archiveGenerator629),
      (.mul archiveGenerator13 archiveGenerator761),
      (.mul archiveGenerator1 archiveGenerator1051),
      (.mul archiveGenerator1 archiveGenerator1050)] (
  .cons [archiveGenerator1082,
      (.mul archiveGenerator24 archiveGenerator628),
      (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051))] (
  .cons [archiveGenerator1081,
      (.mul archiveGenerator23 archiveGenerator628),
      (.mul archiveGenerator8 (.mul archiveGenerator79 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator1063),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator65 archiveGenerator324)))] (
  .cons [archiveGenerator1080,
      archiveGenerator1079,
      (.mul archiveGenerator64 archiveGenerator349),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator294))),
      (.mul archiveGenerator8 archiveGenerator834),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1049))] (
  .cons [archiveGenerator1078,
      (.mul archiveGenerator64 archiveGenerator348),
      (.mul archiveGenerator23 archiveGenerator627),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209))))] (
  .cons [(.mul archiveGenerator138 archiveGenerator209),
      (.mul archiveGenerator17 archiveGenerator690),
      (.mul archiveGenerator8 archiveGenerator832),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator423)))] (
  .cons [(.mul archiveGenerator64 archiveGenerator347),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator627)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator261)))),
      (.mul archiveGenerator2 archiveGenerator1010)] (
  .cons [archiveGenerator1077,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator280))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator168)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator279))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator625)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator420))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator976))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator455))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator301))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator624)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator454)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator160))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator248)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator278)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator299))))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator516),
      (.mul archiveGenerator8 archiveGenerator831),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator0 archiveGenerator1060),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64)))))))] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator380)),
      (.mul archiveGenerator8 archiveGenerator830),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator194)))))] (
  .cons [(.mul archiveGenerator113 archiveGenerator244),
      (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator516)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator193))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator898))))))))))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator343),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator623)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator277)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator919)))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator149)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator149)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator453))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator225))))] (
  .cons [archiveGenerator1076,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator31 archiveGenerator245)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator244)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator452))),
      (.mul archiveGenerator0 archiveGenerator1059)] (
  .cons [(.mul archiveGenerator8 archiveGenerator829),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1033)))] (
  .cons [(.mul archiveGenerator16 archiveGenerator686)] (
  .cons [(.mul archiveGenerator17 archiveGenerator685)] (
  .cons [(.mul archiveGenerator16 archiveGenerator685)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator806))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1030)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator805)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator636))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator969))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1048)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator804)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator803)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1075] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows195 : BasisRows generators 195 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator76 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator70 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator75 archiveGenerator324),
      (.mul archiveGenerator74 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator660)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058)))] (
  .cons [(.mul archiveGenerator73 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator660)))] (
  .cons [(.mul archiveGenerator18 archiveGenerator684)] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator20 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator72 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator659)))] (
  .cons [archiveGenerator1100,
      archiveGenerator1099,
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator324)))] (
  .cons [archiveGenerator1098,
      (.mul archiveGenerator18 archiveGenerator683),
      (.mul archiveGenerator0 archiveGenerator1091),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator66 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator67 archiveGenerator352),
      (.mul archiveGenerator0 archiveGenerator1090),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1072),
      (.mul archiveGenerator0 archiveGenerator1088),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1057)))] (
  .cons [archiveGenerator1097,
      (.mul archiveGenerator3 archiveGenerator965),
      (.mul archiveGenerator1 archiveGenerator1070),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1055)))] (
  .cons [archiveGenerator1096,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1069))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1086),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator336))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1066),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1068))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator532)),
      (.mul archiveGenerator1 archiveGenerator1064),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator960)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator288))),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator857)),
      (.mul archiveGenerator0 (.mul archiveGenerator71 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1064))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator877)),
      (.mul archiveGenerator0 archiveGenerator1084),
      (.mul archiveGenerator0 archiveGenerator1083)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator188)),
      (.mul archiveGenerator4 archiveGenerator930),
      (.mul archiveGenerator1 archiveGenerator1062),
      (.mul archiveGenerator0 archiveGenerator1082),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator287))),
      (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator212)),
      (.mul archiveGenerator0 archiveGenerator1081),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1063))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator286))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator640)),
      (.mul archiveGenerator0 archiveGenerator1079),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator349))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator638)),
      (.mul archiveGenerator0 archiveGenerator1078),
      (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator627))] (
  .cons [archiveGenerator1095,
      (.mul archiveGenerator8 archiveGenerator854),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212)))),
      (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator690)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator832))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator188)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator188)))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator347)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator627)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator187)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator267))))] (
  .cons [archiveGenerator1094,
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator188)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator201)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator435))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator301)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator471))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator113)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator299)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator112)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator80)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator529)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator380)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator637)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator79))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator516))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator898)))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator238)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator154))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator623))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator919))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator237)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator154))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator244)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator46))))))))] (
  .cons [archiveGenerator1093,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator45))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator224))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20))))))))),
      (.mul archiveGenerator0 archiveGenerator1076)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator225)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19))))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1033))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator225)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator136)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1059))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator224)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator56))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1033))))] (
  .cons [(.mul archiveGenerator59 archiveGenerator402),
      (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator403)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator78)))))))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator403)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator77))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator685))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator636)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator283)))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator685))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator635)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator153)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator200)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator199)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator634))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator326)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator470)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator469)))] (
  .cons [archiveGenerator1092] (
  .cons [(.mul archiveGenerator17 archiveGenerator701)] (
  .cons [(.mul archiveGenerator8 archiveGenerator852)] (
  .cons [(.mul archiveGenerator8 archiveGenerator851)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows196 : BasisRows generators 196 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator2 archiveGenerator1058),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1058))] (
  .cons [(.mul archiveGenerator18 (.mul archiveGenerator24 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator75 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator74 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator73 archiveGenerator324))] (
  .cons [] (
  .cons [archiveGenerator1120] (
  .cons [archiveGenerator1119,
      archiveGenerator1118,
      (.mul archiveGenerator1 (.mul archiveGenerator72 archiveGenerator324))] (
  .cons [archiveGenerator1117,
      archiveGenerator1116,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator72 archiveGenerator324)))] (
  .cons [archiveGenerator1115,
      archiveGenerator1114,
      (.mul archiveGenerator43 archiveGenerator544),
      (.mul archiveGenerator2 archiveGenerator1057),
      (.mul archiveGenerator0 archiveGenerator1099)] (
  .cons [(.mul archiveGenerator43 archiveGenerator543),
      (.mul archiveGenerator3 archiveGenerator990),
      (.mul archiveGenerator2 archiveGenerator1055),
      (.mul archiveGenerator1 archiveGenerator1090),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1057)),
      (.mul archiveGenerator0 archiveGenerator1098),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1091)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator66 archiveGenerator324)))))] (
  .cons [archiveGenerator1113,
      archiveGenerator1112,
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator990)),
      (.mul archiveGenerator1 archiveGenerator1088),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1055)),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator352)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324))))))] (
  .cons [archiveGenerator1111,
      (.mul archiveGenerator13 archiveGenerator787),
      (.mul archiveGenerator2 archiveGenerator1054),
      (.mul archiveGenerator1 archiveGenerator1087),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1088)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1057))))] (
  .cons [archiveGenerator1110,
      (.mul archiveGenerator0 archiveGenerator1097),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator965)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator324))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1055))))] (
  .cons [archiveGenerator1109,
      (.mul archiveGenerator67 archiveGenerator363),
      (.mul archiveGenerator1 archiveGenerator1086),
      (.mul archiveGenerator0 archiveGenerator1096),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator324)))))] (
  .cons [archiveGenerator1108,
      archiveGenerator1107,
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator569)),
      (.mul archiveGenerator3 archiveGenerator984),
      (.mul archiveGenerator2 archiveGenerator1052)] (
  .cons [archiveGenerator1106,
      (.mul archiveGenerator18 archiveGenerator690),
      (.mul archiveGenerator3 archiveGenerator982),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1068)))] (
  .cons [(.mul archiveGenerator68 archiveGenerator359),
      (.mul archiveGenerator9 (.mul archiveGenerator75 archiveGenerator212)),
      (.mul archiveGenerator1 (.mul archiveGenerator71 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator351)),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator959)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324)))))))))] (
  .cons [archiveGenerator1105,
      (.mul archiveGenerator67 archiveGenerator359),
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator417)),
      (.mul archiveGenerator1 archiveGenerator1083),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator71 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1064)))] (
  .cons [archiveGenerator1104,
      (.mul archiveGenerator1 archiveGenerator1082),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1083))] (
  .cons [(.mul archiveGenerator3 archiveGenerator978),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1082)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1080),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1081)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1063)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1079)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator349)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator75))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1078)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator627)))] (
  .cons [archiveGenerator1103,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator537)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator105))))),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator347)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator832)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator784),
      (.mul archiveGenerator1 archiveGenerator1077),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator347))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator627))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator864)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator642))] (
  .cons [(.mul archiveGenerator8 archiveGenerator863),
      (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator260))] (
  .cons [archiveGenerator1102] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator516)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator898))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator623)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator919)))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1093)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1076))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1059)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1033)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator403)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator403))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator685)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator636))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator685)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator635)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator701))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator852))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator851))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1101] (
  .cons [(.mul archiveGenerator1 archiveGenerator1075)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows197 : BasisRows generators 197 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator70 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1058))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator660)),
      (.mul archiveGenerator1 (.mul archiveGenerator76 archiveGenerator324))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator660))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator74 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058)))))] (
  .cons [(.mul archiveGenerator80 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator684)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator73 archiveGenerator324)))] (
  .cons [archiveGenerator1138,
      archiveGenerator1137,
      (.mul archiveGenerator79 archiveGenerator324)] (
  .cons [archiveGenerator1136,
      (.mul archiveGenerator0 archiveGenerator1120)] (
  .cons [archiveGenerator1135,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator324))),
      (.mul archiveGenerator0 archiveGenerator1118)] (
  .cons [archiveGenerator1134,
      archiveGenerator1133,
      archiveGenerator1132,
      (.mul archiveGenerator8 (.mul archiveGenerator46 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1100),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator72 archiveGenerator324))))] (
  .cons [archiveGenerator1131,
      archiveGenerator1130,
      (.mul archiveGenerator67 archiveGenerator376),
      (.mul archiveGenerator8 (.mul archiveGenerator45 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator544)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1057)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1099))] (
  .cons [archiveGenerator1129,
      (.mul archiveGenerator67 archiveGenerator373),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator543)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1098)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator66 archiveGenerator324))))))] (
  .cons [archiveGenerator1128,
      (.mul archiveGenerator76 archiveGenerator335),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator19 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1004),
      (.mul archiveGenerator0 archiveGenerator1113),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324)))))))] (
  .cons [archiveGenerator1127,
      (.mul archiveGenerator75 archiveGenerator335),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1004)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1088))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1057)))))] (
  .cons [archiveGenerator1126,
      (.mul archiveGenerator1 archiveGenerator1096),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1055)))))] (
  .cons [archiveGenerator1125,
      (.mul archiveGenerator78 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator363))] (
  .cons [archiveGenerator1124,
      (.mul archiveGenerator77 archiveGenerator324),
      (.mul archiveGenerator0 archiveGenerator1108),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator984))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator690)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator982))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator359)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324))))))))))] (
  .cons [archiveGenerator1123,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator181)))),
      (.mul archiveGenerator8 (.mul archiveGenerator89 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator1105),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator359))] (
  .cons [archiveGenerator1122,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator294))),
      (.mul archiveGenerator8 archiveGenerator878),
      (.mul archiveGenerator0 archiveGenerator1104),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1083)))] (
  .cons [(.mul archiveGenerator23 archiveGenerator655),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator250)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209)))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator978)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator383),
      (.mul archiveGenerator8 archiveGenerator874),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator423))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1081))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1063))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator382),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator655)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator261)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1079))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator349))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator294)))),
      (.mul archiveGenerator1 archiveGenerator1095),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator627))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator209))))),
      (.mul archiveGenerator0 archiveGenerator1103),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator209))))] (
  .cons [(.mul archiveGenerator113 archiveGenerator260),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator293)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator347))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator380),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator492))),
      (.mul archiveGenerator1 archiveGenerator1094)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator347))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator292))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator347))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator248)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator291))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator60 archiveGenerator260)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator653)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator167)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator245)),
      (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator260))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator194)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator149)),
      (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator260))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator208)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator244)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator491))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator207)))))] (
  .cons [archiveGenerator1121,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator160)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator206)))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator725),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator490))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator919))))))))))))))] (
  .cons [(.mul archiveGenerator16 archiveGenerator725),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator489)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator343)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator488)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator873),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1076)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator872)] (
  .cons [(.mul archiveGenerator17 archiveGenerator722),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1059))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator871),
      (.mul archiveGenerator1 (.mul archiveGenerator59 archiveGenerator402)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1033))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator403))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator685))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator636))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator635))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator916)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator852)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator851)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1101)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows198 : BasisRows generators 198 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator86 archiveGenerator324),
      (.mul archiveGenerator2 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator341))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1058)))] (
  .cons [archiveGenerator1166,
      (.mul archiveGenerator85 archiveGenerator324),
      (.mul archiveGenerator84 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator660)))] (
  .cons [archiveGenerator1165,
      (.mul archiveGenerator83 archiveGenerator324),
      (.mul archiveGenerator82 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324))))))))] (
  .cons [archiveGenerator1164,
      (.mul archiveGenerator81 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058))))))] (
  .cons [archiveGenerator1163,
      archiveGenerator1162,
      (.mul archiveGenerator0 (.mul archiveGenerator80 archiveGenerator324))] (
  .cons [archiveGenerator1161,
      (.mul archiveGenerator0 archiveGenerator1138),
      (.mul archiveGenerator0 (.mul archiveGenerator79 archiveGenerator324))] (
  .cons [archiveGenerator1160,
      (.mul archiveGenerator1 archiveGenerator1118),
      (.mul archiveGenerator0 archiveGenerator1136),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1120))] (
  .cons [archiveGenerator1159,
      (.mul archiveGenerator67 archiveGenerator397),
      (.mul archiveGenerator0 archiveGenerator1135),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1118))] (
  .cons [archiveGenerator1158,
      (.mul archiveGenerator67 archiveGenerator392),
      (.mul archiveGenerator0 archiveGenerator1133),
      (.mul archiveGenerator0 archiveGenerator1132)] (
  .cons [archiveGenerator1157,
      (.mul archiveGenerator3 archiveGenerator1020),
      (.mul archiveGenerator2 archiveGenerator1088),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1090)),
      (.mul archiveGenerator0 archiveGenerator1131),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1057)))] (
  .cons [archiveGenerator1156,
      (.mul archiveGenerator3 archiveGenerator1017),
      (.mul archiveGenerator1 archiveGenerator1112),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1088)),
      (.mul archiveGenerator0 archiveGenerator1129),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator66 archiveGenerator324)))))))] (
  .cons [archiveGenerator1155,
      archiveGenerator1154,
      (.mul archiveGenerator3 archiveGenerator1016),
      (.mul archiveGenerator3 archiveGenerator1015),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324))))))))] (
  .cons [archiveGenerator1153,
      archiveGenerator1152,
      (.mul archiveGenerator3 archiveGenerator1014)] (
  .cons [archiveGenerator1151,
      archiveGenerator1150,
      (.mul archiveGenerator3 archiveGenerator1011),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1086))] (
  .cons [archiveGenerator1149,
      archiveGenerator1148,
      (.mul archiveGenerator1 archiveGenerator1107),
      (.mul archiveGenerator0 (.mul archiveGenerator78 archiveGenerator324))] (
  .cons [archiveGenerator1147,
      (.mul archiveGenerator0 (.mul archiveGenerator77 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1108))] (
  .cons [archiveGenerator1146,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator331))),
      (.mul archiveGenerator2 archiveGenerator1083),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator71 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator190)))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1083)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator359))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324)))))))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator359)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator189)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator640)),
      (.mul archiveGenerator0 archiveGenerator1122),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188)))),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator328))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator668)),
      (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator655)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator978))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator303))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator667)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator874)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1081)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1063)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator255)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator655))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1079)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator349)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator254)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator267)))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator347))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator627)))))] (
  .cons [archiveGenerator1145,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1103)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator209)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator404),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator52)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator212))))),
      (.mul archiveGenerator0 (.mul archiveGenerator113 archiveGenerator260)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator347)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator435))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator380))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator499))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator299)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator80))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator64))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator89))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator665)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator80))))))),
      (.mul archiveGenerator5 (.mul archiveGenerator149 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator664)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator89))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator138))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator162))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator137))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator113)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))))] (
  .cons [archiveGenerator1144,
      archiveGenerator1143,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator147)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator51))))))))] (
  .cons [(.mul archiveGenerator138 archiveGenerator225),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator146)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator23))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator725))] (
  .cons [(.mul archiveGenerator64 archiveGenerator403),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator185)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator22))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator725))] (
  .cons [(.mul archiveGenerator64 archiveGenerator402),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator238)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator8))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator298)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator88)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator297)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator17))))))))] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator433)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator556)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1059)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator663)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator211))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1033)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator662)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator111)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator403)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator111)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator685)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator145))))))] (
  .cons [archiveGenerator1142,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator498)))] (
  .cons [archiveGenerator1141,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator183))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator296))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator295))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator886)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator554))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator554))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator661))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1140] (
  .cons [archiveGenerator1139] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1101))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows199 : BasisRows generators 199 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator76 archiveGenerator324))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator75 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator86 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator84 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator660))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1165),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator324)))))))))] (
  .cons [archiveGenerator1178,
      (.mul archiveGenerator0 (.mul archiveGenerator81 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058)))))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator79 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1163),
      (.mul archiveGenerator0 archiveGenerator1162),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator80 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1161),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator79 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator924),
      (.mul archiveGenerator0 archiveGenerator1160)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1159),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator397)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1118)))] (
  .cons [archiveGenerator1177,
      (.mul archiveGenerator0 archiveGenerator1158),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator392)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1133))] (
  .cons [archiveGenerator1176,
      (.mul archiveGenerator0 archiveGenerator1157),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1020)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1088)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1131))] (
  .cons [archiveGenerator1175,
      (.mul archiveGenerator9 archiveGenerator867),
      (.mul archiveGenerator1 archiveGenerator1128),
      (.mul archiveGenerator1 (.mul archiveGenerator76 archiveGenerator335)),
      (.mul archiveGenerator0 archiveGenerator1156),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1017)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1129)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator66 archiveGenerator324))))))))] (
  .cons [archiveGenerator1174,
      (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator213)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator570)),
      (.mul archiveGenerator3 archiveGenerator1042),
      (.mul archiveGenerator2 archiveGenerator1096),
      (.mul archiveGenerator1 archiveGenerator1127),
      (.mul archiveGenerator0 archiveGenerator1154),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1016)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1015)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator324)))))))))] (
  .cons [archiveGenerator1173,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator569)),
      (.mul archiveGenerator1 archiveGenerator1126),
      (.mul archiveGenerator0 archiveGenerator1153),
      (.mul archiveGenerator0 archiveGenerator1152),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1014))] (
  .cons [archiveGenerator1172,
      (.mul archiveGenerator76 archiveGenerator359),
      (.mul archiveGenerator13 (.mul archiveGenerator76 archiveGenerator212)),
      (.mul archiveGenerator0 archiveGenerator1150),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1011))] (
  .cons [(.mul archiveGenerator74 archiveGenerator359),
      (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator212)),
      (.mul archiveGenerator3 archiveGenerator1037),
      (.mul archiveGenerator0 archiveGenerator1149),
      (.mul archiveGenerator0 archiveGenerator1148),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator78 archiveGenerator324)))] (
  .cons [archiveGenerator1171,
      (.mul archiveGenerator64 archiveGenerator418),
      (.mul archiveGenerator13 archiveGenerator822),
      (.mul archiveGenerator0 archiveGenerator1147),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator77 archiveGenerator324)))] (
  .cons [archiveGenerator1170,
      (.mul archiveGenerator87 archiveGenerator324),
      (.mul archiveGenerator0 archiveGenerator1146),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1083))] (
  .cons [archiveGenerator1169,
      archiveGenerator1168,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator324))))))))))))] (
  .cons [(.mul archiveGenerator149 archiveGenerator209),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator76))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator75))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator874))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1063))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1079))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator349))))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator864)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator642)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator209))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator890),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator404)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator113 archiveGenerator260))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator347))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator889),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator380)))] (
  .cons [archiveGenerator1167] (
  .cons [(.mul archiveGenerator149 archiveGenerator206)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator260)))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1121),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator491)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1143)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator225)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator725)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator725)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator402))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator556))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1059))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator663))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1033))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator662))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator403))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator685))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1142)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1141)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator916))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator554)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator661)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1140)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1139)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows200 : BasisRows generators 200 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator94 archiveGenerator324),
      (.mul archiveGenerator3 archiveGenerator1058)] (
  .cons [(.mul archiveGenerator93 archiveGenerator324),
      (.mul archiveGenerator92 archiveGenerator324),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1058))] (
  .cons [(.mul archiveGenerator91 archiveGenerator324)] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator324)),
      (.mul archiveGenerator2 (.mul archiveGenerator18 (.mul archiveGenerator24 archiveGenerator324)))] (
  .cons [archiveGenerator1201,
      (.mul archiveGenerator3 (.mul archiveGenerator67 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator75 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator86 archiveGenerator324)))] (
  .cons [archiveGenerator1200,
      (.mul archiveGenerator1 archiveGenerator1165),
      (.mul archiveGenerator1 (.mul archiveGenerator82 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator84 archiveGenerator324)))] (
  .cons [archiveGenerator1199,
      archiveGenerator1198,
      archiveGenerator1197,
      (.mul archiveGenerator90 archiveGenerator324),
      (.mul archiveGenerator89 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator81 archiveGenerator324))] (
  .cons [archiveGenerator1196,
      (.mul archiveGenerator23 (.mul archiveGenerator24 archiveGenerator324)),
      (.mul archiveGenerator2 archiveGenerator1120),
      (.mul archiveGenerator1 archiveGenerator1163),
      (.mul archiveGenerator1 archiveGenerator1162),
      (.mul archiveGenerator0 archiveGenerator1178),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator81 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058))))))))] (
  .cons [archiveGenerator1195,
      archiveGenerator1194,
      archiveGenerator1193,
      (.mul archiveGenerator76 archiveGenerator376),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator324))),
      (.mul archiveGenerator2 archiveGenerator1118),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1162)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator80 archiveGenerator324))))] (
  .cons [archiveGenerator1192,
      archiveGenerator1191,
      archiveGenerator1190,
      (.mul archiveGenerator75 archiveGenerator376),
      (.mul archiveGenerator8 (.mul archiveGenerator51 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1057),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1118)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1161))] (
  .cons [archiveGenerator1189,
      archiveGenerator1188,
      archiveGenerator1187,
      (.mul archiveGenerator75 archiveGenerator373),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1056),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1057)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1160))] (
  .cons [archiveGenerator1186,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator324))),
      (.mul archiveGenerator1 archiveGenerator1158),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1159))] (
  .cons [archiveGenerator1185,
      archiveGenerator1184,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator88 archiveGenerator324),
      (.mul archiveGenerator7 archiveGenerator932),
      (.mul archiveGenerator1 archiveGenerator1156)] (
  .cons [archiveGenerator1183,
      (.mul archiveGenerator1 archiveGenerator1154),
      (.mul archiveGenerator0 archiveGenerator1175),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1156))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator50 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1153),
      (.mul archiveGenerator1 archiveGenerator1152),
      (.mul archiveGenerator0 archiveGenerator1174),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1154)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1015)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator49 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1153)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1152)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1014)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator880),
      (.mul archiveGenerator7 archiveGenerator930),
      (.mul archiveGenerator3 archiveGenerator1050),
      (.mul archiveGenerator1 archiveGenerator1148),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1150))] (
  .cons [(.mul archiveGenerator23 archiveGenerator691),
      (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator74 archiveGenerator359)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1037)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator101 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator1171),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator418)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1147)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator77 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator833),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator692)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1146)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1083)))] (
  .cons [archiveGenerator1182,
      (.mul archiveGenerator23 archiveGenerator690),
      (.mul archiveGenerator9 archiveGenerator876),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209)))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator261)),
      (.mul archiveGenerator0 archiveGenerator1169)] (
  .cons [(.mul archiveGenerator16 archiveGenerator760),
      (.mul archiveGenerator13 archiveGenerator832),
      (.mul archiveGenerator8 archiveGenerator901),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator423))),
      (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105))))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator209)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator690)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator261)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084))))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator420),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator294)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051))))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator209))))),
      (.mul archiveGenerator2 archiveGenerator1103)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator150)))),
      (.mul archiveGenerator8 archiveGenerator897),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator293)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator349)))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194)))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator260)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator316))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator318))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator518))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator292)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator209)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator248)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator517))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator316)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator347)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator380)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator689)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator380))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator278))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator688)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator194)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator160)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator380))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator219)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator257)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator516))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator218))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator149 archiveGenerator149)))] (
  .cons [archiveGenerator1181,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator167)))))] (
  .cons [archiveGenerator1180,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator149))))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator759),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator315))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator896),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator245)))),
      (.mul archiveGenerator1 archiveGenerator1143)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator244)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1143))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator244)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator725))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator687)),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator402)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator686)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator402)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator452))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator685))] (
  .cons [archiveGenerator1179] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator663))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator403)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1142))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1141))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator554))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator661))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1139),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1140))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1139))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows201 : BasisRows generators 201 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator96 archiveGenerator324)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator94 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1058))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator93 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator92 archiveGenerator324))] (
  .cons [(.mul archiveGenerator95 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator91 archiveGenerator324))] (
  .cons [archiveGenerator1217,
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator324)))] (
  .cons [archiveGenerator1216,
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator67 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator80 archiveGenerator324))] (
  .cons [archiveGenerator1215,
      (.mul archiveGenerator0 archiveGenerator1198),
      (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator89 archiveGenerator324))] (
  .cons [archiveGenerator1214,
      archiveGenerator1213,
      archiveGenerator1212,
      archiveGenerator1211,
      (.mul archiveGenerator0 archiveGenerator1196),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1178)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator81 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058)))))))))] (
  .cons [(.mul archiveGenerator92 archiveGenerator333),
      (.mul archiveGenerator0 archiveGenerator1195),
      (.mul archiveGenerator0 archiveGenerator1194),
      (.mul archiveGenerator0 archiveGenerator1193),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1118)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1162))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator80 archiveGenerator324)))))] (
  .cons [archiveGenerator1210,
      (.mul archiveGenerator0 archiveGenerator1191),
      (.mul archiveGenerator0 archiveGenerator1190),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1161)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1188),
      (.mul archiveGenerator0 archiveGenerator1187),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1056))] (
  .cons [archiveGenerator1209,
      archiveGenerator1208,
      (.mul archiveGenerator1 archiveGenerator1177),
      (.mul archiveGenerator0 archiveGenerator1186)] (
  .cons [archiveGenerator1207,
      archiveGenerator1206,
      (.mul archiveGenerator0 archiveGenerator1185),
      (.mul archiveGenerator0 archiveGenerator1184)] (
  .cons [(.mul archiveGenerator3 archiveGenerator1068),
      (.mul archiveGenerator3 archiveGenerator1067),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator932))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1174),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1042)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1175))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1064),
      (.mul archiveGenerator1 archiveGenerator1173),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator50 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1154)))] (
  .cons [archiveGenerator1205,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator332))),
      (.mul archiveGenerator1 (.mul archiveGenerator76 archiveGenerator359)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator49 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator331))),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator930)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1150)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator941),
      (.mul archiveGenerator1 archiveGenerator1171),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1149)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator212)),
      (.mul archiveGenerator2 archiveGenerator1123),
      (.mul archiveGenerator1 (.mul archiveGenerator87 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator418))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1147)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator581)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator640)),
      (.mul archiveGenerator1 archiveGenerator1168),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1146)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator328))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator705)),
      (.mul archiveGenerator1 (.mul archiveGenerator149 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator1182),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1169))] (
  .cons [archiveGenerator1204,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator704)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator901)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator690))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator187))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator267)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051)))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))))),
      (.mul archiveGenerator8 archiveGenerator920),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator5 archiveGenerator963)] (
  .cons [(.mul archiveGenerator64 archiveGenerator434),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator212))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator897))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator530))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator255)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator327)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator72))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator101))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator404))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator80)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator529))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator101)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator185))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator64)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator184))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator154)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator778),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator51)))))))),
      (.mul archiveGenerator0 archiveGenerator1180)] (
  .cons [(.mul archiveGenerator8 archiveGenerator918),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator23))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator759))] (
  .cons [(.mul archiveGenerator64 archiveGenerator433),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator29))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator896))] (
  .cons [(.mul archiveGenerator64 archiveGenerator432),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator138))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator9)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1143)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator225))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator100))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator725)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator224))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator40)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator402)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator56)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator402))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator403))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator55))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator403))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator223)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator402))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator117))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator153))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator152))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator917),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator528)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator916),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator253))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator326))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator325))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator915),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1141)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator579))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator701))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator700))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1203] (
  .cons [archiveGenerator1202] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1140)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows202 : BasisRows generators 202 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator99 archiveGenerator324)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1058)),
      (.mul archiveGenerator0 (.mul archiveGenerator96 archiveGenerator324))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator92 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1058)))] (
  .cons [archiveGenerator1237,
      (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator446)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator92 archiveGenerator324)))] (
  .cons [archiveGenerator1236,
      archiveGenerator1235,
      (.mul archiveGenerator2 archiveGenerator1166),
      (.mul archiveGenerator0 (.mul archiveGenerator95 archiveGenerator324))] (
  .cons [archiveGenerator1234,
      archiveGenerator1233,
      (.mul archiveGenerator2 (.mul archiveGenerator82 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1217),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator324))))] (
  .cons [archiveGenerator1232,
      archiveGenerator1231,
      archiveGenerator1230,
      (.mul archiveGenerator98 archiveGenerator324),
      (.mul archiveGenerator0 archiveGenerator1216),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator67 archiveGenerator324))))] (
  .cons [archiveGenerator1229,
      archiveGenerator1228,
      archiveGenerator1227,
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator81 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator80 archiveGenerator324)))] (
  .cons [archiveGenerator1226,
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1163)),
      (.mul archiveGenerator0 archiveGenerator1215),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator89 archiveGenerator324)))] (
  .cons [archiveGenerator1225,
      (.mul archiveGenerator3 archiveGenerator1091),
      (.mul archiveGenerator0 archiveGenerator1212),
      (.mul archiveGenerator0 archiveGenerator1211),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator81 archiveGenerator324))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058))))))))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1192),
      (.mul archiveGenerator0 (.mul archiveGenerator92 archiveGenerator333)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1195)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1162)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator80 archiveGenerator324))))))] (
  .cons [archiveGenerator1224,
      (.mul archiveGenerator3 archiveGenerator1088),
      (.mul archiveGenerator1 archiveGenerator1187),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1190))] (
  .cons [archiveGenerator1223,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1188)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1187))] (
  .cons [archiveGenerator1222,
      (.mul archiveGenerator13 archiveGenerator867),
      (.mul archiveGenerator0 archiveGenerator1209),
      (.mul archiveGenerator0 archiveGenerator1208),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1186))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator88 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator932)),
      (.mul archiveGenerator0 archiveGenerator1207),
      (.mul archiveGenerator0 archiveGenerator1206),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1185)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1184))] (
  .cons [(.mul archiveGenerator2 archiveGenerator1152),
      (.mul archiveGenerator1 archiveGenerator1183),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1154)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1068)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1067))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator373))),
      (.mul archiveGenerator2 archiveGenerator1151),
      (.mul archiveGenerator2 archiveGenerator1150),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1153)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1152)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1175)))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator959)),
      (.mul archiveGenerator2 archiveGenerator1148),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1064)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator50 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1154))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator619)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator930)),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1050)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1148)),
      (.mul archiveGenerator0 archiveGenerator1205),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator49 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator335))),
      (.mul archiveGenerator3 archiveGenerator1082),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator930))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1150))))] (
  .cons [archiveGenerator1221,
      (.mul archiveGenerator3 archiveGenerator1081),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1149))))] (
  .cons [(.mul archiveGenerator160 archiveGenerator209),
      (.mul archiveGenerator97 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator418)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1147))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1182),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1146))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1182)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1169)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator133))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator901))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator209)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105))))))] (
  .cons [archiveGenerator1220,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator585)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator83))))),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator420)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084))))))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator864),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator642))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator715)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator897)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator928),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator927)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator149 archiveGenerator149))] (
  .cons [archiveGenerator1219,
      archiveGenerator1218] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator918)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator759)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator433)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator896)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator432)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1143))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator402))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator725))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator402)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1179),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator403))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator402))))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator969)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator917))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator916))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1203)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1202)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1139))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1140))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows203 : BasisRows generators 203 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator96 archiveGenerator324))] (
  .cons [(.mul archiveGenerator4 archiveGenerator1058),
      (.mul archiveGenerator3 (.mul archiveGenerator76 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator96 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator74 archiveGenerator324)),
      (.mul archiveGenerator2 (.mul archiveGenerator2 (.mul archiveGenerator76 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1058))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator95 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator446)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1236)] (
  .cons [archiveGenerator1252,
      (.mul archiveGenerator101 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1217))] (
  .cons [(.mul archiveGenerator7 archiveGenerator968),
      (.mul archiveGenerator0 archiveGenerator1232),
      (.mul archiveGenerator0 archiveGenerator1230)] (
  .cons [(.mul archiveGenerator1 archiveGenerator1215),
      (.mul archiveGenerator0 archiveGenerator1229),
      (.mul archiveGenerator0 archiveGenerator1228),
      (.mul archiveGenerator0 archiveGenerator1227)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator51 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1099),
      (.mul archiveGenerator1 archiveGenerator1214),
      (.mul archiveGenerator1 archiveGenerator1213),
      (.mul archiveGenerator1 archiveGenerator1211),
      (.mul archiveGenerator0 archiveGenerator1226),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1215)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324))))] (
  .cons [archiveGenerator1251,
      archiveGenerator1250,
      archiveGenerator1249,
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1098),
      (.mul archiveGenerator0 archiveGenerator1225),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1091)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1058)))))))))))] (
  .cons [archiveGenerator1248,
      (.mul archiveGenerator174 archiveGenerator197),
      (.mul archiveGenerator92 archiveGenerator351),
      (.mul archiveGenerator9 archiveGenerator912),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator29 archiveGenerator324))),
      (.mul archiveGenerator7 archiveGenerator967),
      (.mul archiveGenerator4 archiveGenerator1057),
      (.mul archiveGenerator3 (.mul archiveGenerator67 archiveGenerator352)),
      (.mul archiveGenerator1 archiveGenerator1210)] (
  .cons [archiveGenerator1247,
      archiveGenerator1246,
      (.mul archiveGenerator23 archiveGenerator734),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator324)))),
      (.mul archiveGenerator7 archiveGenerator965),
      (.mul archiveGenerator0 archiveGenerator1224),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1088))] (
  .cons [(.mul archiveGenerator100 archiveGenerator324),
      (.mul archiveGenerator76 archiveGenerator417),
      (.mul archiveGenerator3 archiveGenerator1097),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator965)),
      (.mul archiveGenerator1 archiveGenerator1208),
      (.mul archiveGenerator0 archiveGenerator1223)] (
  .cons [archiveGenerator1245,
      (.mul archiveGenerator75 archiveGenerator417),
      (.mul archiveGenerator17 (.mul archiveGenerator40 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1222),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1209))] (
  .cons [(.mul archiveGenerator43 archiveGenerator604),
      (.mul archiveGenerator8 (.mul archiveGenerator56 archiveGenerator324)),
      (.mul archiveGenerator7 archiveGenerator964),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1207))] (
  .cons [archiveGenerator1244,
      archiveGenerator1243,
      (.mul archiveGenerator8 (.mul archiveGenerator55 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1152))] (
  .cons [archiveGenerator1242,
      (.mul archiveGenerator13 archiveGenerator880),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1150)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1175))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1064))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1154)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator101 archiveGenerator209))] (
  .cons [(.mul archiveGenerator13 archiveGenerator877),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator67 archiveGenerator75)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator692)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1150)))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator876),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator729)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1081)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1149)))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator901),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator280)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator423))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator418))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1147)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator279)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator690)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator261)))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator149 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1146)))))] (
  .cons [(.mul archiveGenerator72 archiveGenerator420),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator294)))),
      (.mul archiveGenerator1 archiveGenerator1204),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1182))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1169))))] (
  .cons [(.mul archiveGenerator113 archiveGenerator292),
      (.mul archiveGenerator64 archiveGenerator455),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator209))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator209))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator940),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator350)))),
      (.mul archiveGenerator0 archiveGenerator1220),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator278)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator348)))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator963)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1051)))))))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator550))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator292))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator248)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator347)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator346))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator260))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator549))),
      (.mul archiveGenerator5 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator726)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator194)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator598)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator260)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator219)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator149))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator260)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator233))))),
      (.mul archiveGenerator0 archiveGenerator1218)] (
  .cons [(.mul archiveGenerator137 archiveGenerator246),
      (.mul archiveGenerator60 archiveGenerator491),
      (.mul archiveGenerator59 archiveGenerator491),
      (.mul archiveGenerator8 archiveGenerator939),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator232)))))] (
  .cons [(.mul archiveGenerator137 archiveGenerator245),
      (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator491)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator160))))))] (
  .cons [(.mul archiveGenerator138 archiveGenerator244),
      (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator491)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator345))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator452),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator725)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator344))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator257))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator343))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator724)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator433)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator723)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1143)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator595))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator722)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403))))))] (
  .cons [archiveGenerator1241,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator402))))))] (
  .cons [archiveGenerator1240] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator403)))))] (
  .cons [archiveGenerator1239] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator917)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator916)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1203))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1202))] (
  .cons [archiveGenerator1238] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1140)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows204 : BasisRows generators 204 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator99 archiveGenerator324))] (
  .cons [archiveGenerator1286,
      (.mul archiveGenerator2 (.mul archiveGenerator92 archiveGenerator324))] (
  .cons [archiveGenerator1285,
      archiveGenerator1284,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator96 archiveGenerator324))))] (
  .cons [archiveGenerator1283,
      archiveGenerator1282,
      archiveGenerator1281,
      (.mul archiveGenerator107 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator446))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator74 archiveGenerator324)))] (
  .cons [archiveGenerator1280,
      archiveGenerator1279,
      archiveGenerator1278,
      (.mul archiveGenerator106 archiveGenerator324),
      (.mul archiveGenerator105 archiveGenerator324),
      (.mul archiveGenerator1 archiveGenerator1235)] (
  .cons [archiveGenerator1277,
      archiveGenerator1276,
      archiveGenerator1275,
      (.mul archiveGenerator104 archiveGenerator324),
      (.mul archiveGenerator103 archiveGenerator324),
      (.mul archiveGenerator92 archiveGenerator368)] (
  .cons [archiveGenerator1274,
      archiveGenerator1273,
      (.mul archiveGenerator3 archiveGenerator1120),
      (.mul archiveGenerator2 archiveGenerator1197),
      (.mul archiveGenerator1 (.mul archiveGenerator98 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1252),
      (.mul archiveGenerator0 (.mul archiveGenerator101 archiveGenerator324))] (
  .cons [archiveGenerator1272,
      archiveGenerator1271,
      (.mul archiveGenerator92 archiveGenerator367),
      (.mul archiveGenerator3 archiveGenerator1118),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1232))] (
  .cons [archiveGenerator1270,
      (.mul archiveGenerator92 archiveGenerator366),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1118)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1227))] (
  .cons [archiveGenerator1269,
      archiveGenerator1268,
      (.mul archiveGenerator2 (.mul archiveGenerator75 archiveGenerator376)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1215))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324)))))] (
  .cons [archiveGenerator1267,
      archiveGenerator1266,
      (.mul archiveGenerator190 archiveGenerator190),
      (.mul archiveGenerator7 archiveGenerator988),
      (.mul archiveGenerator0 archiveGenerator1249),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1091)))] (
  .cons [archiveGenerator1265,
      archiveGenerator1264,
      archiveGenerator1263,
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1088)),
      (.mul archiveGenerator0 archiveGenerator1248),
      (.mul archiveGenerator0 (.mul archiveGenerator92 archiveGenerator351)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator67 archiveGenerator352)))] (
  .cons [archiveGenerator1262,
      archiveGenerator1261,
      (.mul archiveGenerator189 archiveGenerator190),
      (.mul archiveGenerator0 archiveGenerator1247),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator965)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1224)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1088)))] (
  .cons [archiveGenerator1260,
      (.mul archiveGenerator188 archiveGenerator190),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1097)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator965))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1223))] (
  .cons [archiveGenerator1259,
      (.mul archiveGenerator189 archiveGenerator189),
      (.mul archiveGenerator0 archiveGenerator1245),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator40 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1222))] (
  .cons [archiveGenerator1258,
      archiveGenerator1257,
      (.mul archiveGenerator188 archiveGenerator189),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator604)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator56 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator964)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1207)))] (
  .cons [(.mul archiveGenerator188 archiveGenerator188),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator982)),
      (.mul archiveGenerator0 archiveGenerator1244),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator55 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1152)))] (
  .cons [(.mul archiveGenerator187 archiveGenerator188),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1175)))))] (
  .cons [(.mul archiveGenerator187 archiveGenerator187),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator408))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1154))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator213))))] (
  .cons [(.mul archiveGenerator102 archiveGenerator324),
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator640))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator360))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator705)),
      (.mul archiveGenerator1 (.mul archiveGenerator97 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator876)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1149))))))] (
  .cons [archiveGenerator1256,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212)))),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator286))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator738)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator418)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1147))))))] (
  .cons [archiveGenerator1255,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator357))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1146))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator201))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator267)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1169)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator957),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator0 (.mul archiveGenerator113 archiveGenerator292)),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator455)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105))))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))))),
      (.mul archiveGenerator8 archiveGenerator956),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator212))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator940)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084))))))))))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator113)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator24))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator267)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator278)))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator112)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator188)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator188)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator187))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator101))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator559))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator80)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator557))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator101))))))),
      (.mul archiveGenerator1 archiveGenerator1218)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator138)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator113)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1218))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator137)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator162)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator246)),
      (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator491))] (
  .cons [(.mul archiveGenerator8 archiveGenerator955),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator113))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator51)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator491)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator954),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator112))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator23))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator244)),
      (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator491)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator225)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator147))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator32))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator452)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator725)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator224)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator185))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator13))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator238))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator60))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator237))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator17)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator298))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1143))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator433))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator556))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator161)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator555))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator50))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator402)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator111))))))),
      (.mul archiveGenerator0 archiveGenerator1240)] (
  .cons [(.mul archiveGenerator17 archiveGenerator806),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator110)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator953),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator354)))),
      (.mul archiveGenerator0 archiveGenerator1239)] (
  .cons [(.mul archiveGenerator8 archiveGenerator952),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator183))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator969))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator183)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator236)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator736))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator296)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator554)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator553)))] (
  .cons [archiveGenerator1254,
      archiveGenerator1253] (
  .cons [(.mul archiveGenerator17 archiveGenerator804)] (
  .cons [(.mul archiveGenerator16 archiveGenerator804)] (
  .cons [(.mul archiveGenerator8 archiveGenerator951)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1202)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows205 : BasisRows generators 205 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1299,
      (.mul archiveGenerator109 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator96 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator4 archiveGenerator1058)),
      (.mul archiveGenerator1 (.mul archiveGenerator3 (.mul archiveGenerator76 archiveGenerator324))),
      (.mul archiveGenerator0 archiveGenerator1286),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator92 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator108 archiveGenerator324),
      (.mul archiveGenerator2 (.mul archiveGenerator95 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1284)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1283),
      (.mul archiveGenerator0 archiveGenerator1281),
      (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1280),
      (.mul archiveGenerator0 archiveGenerator1279),
      (.mul archiveGenerator0 archiveGenerator1278),
      (.mul archiveGenerator0 (.mul archiveGenerator106 archiveGenerator324))] (
  .cons [archiveGenerator1298,
      (.mul archiveGenerator0 archiveGenerator1277),
      (.mul archiveGenerator0 archiveGenerator1276),
      (.mul archiveGenerator0 archiveGenerator1275),
      (.mul archiveGenerator0 (.mul archiveGenerator104 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator103 archiveGenerator324))] (
  .cons [(.mul archiveGenerator18 (.mul archiveGenerator40 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1136),
      (.mul archiveGenerator2 archiveGenerator1215),
      (.mul archiveGenerator0 archiveGenerator1273),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1120)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator101 archiveGenerator324)))] (
  .cons [archiveGenerator1297,
      archiveGenerator1296,
      (.mul archiveGenerator3 archiveGenerator1135),
      (.mul archiveGenerator0 archiveGenerator1271),
      (.mul archiveGenerator0 (.mul archiveGenerator92 archiveGenerator367)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1118))] (
  .cons [archiveGenerator1295,
      archiveGenerator1294,
      (.mul archiveGenerator3 archiveGenerator1133),
      (.mul archiveGenerator3 archiveGenerator1132),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1211)),
      (.mul archiveGenerator0 archiveGenerator1270),
      (.mul archiveGenerator0 (.mul archiveGenerator92 archiveGenerator366))] (
  .cons [archiveGenerator1293,
      (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1131),
      (.mul archiveGenerator0 archiveGenerator1269),
      (.mul archiveGenerator0 archiveGenerator1268),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324))))))] (
  .cons [archiveGenerator1292,
      (.mul archiveGenerator107 archiveGenerator333),
      (.mul archiveGenerator3 archiveGenerator1129),
      (.mul archiveGenerator1 (.mul archiveGenerator4 archiveGenerator1057)),
      (.mul archiveGenerator0 archiveGenerator1267)] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator76 archiveGenerator335)),
      (.mul archiveGenerator1 archiveGenerator1247),
      (.mul archiveGenerator1 archiveGenerator1246),
      (.mul archiveGenerator0 archiveGenerator1265),
      (.mul archiveGenerator0 archiveGenerator1263)] (
  .cons [(.mul archiveGenerator9 archiveGenerator933),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1208)),
      (.mul archiveGenerator0 archiveGenerator1262),
      (.mul archiveGenerator0 archiveGenerator1261),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1088))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator95 archiveGenerator213)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator376))),
      (.mul archiveGenerator7 archiveGenerator1000),
      (.mul archiveGenerator3 archiveGenerator1126),
      (.mul archiveGenerator1 archiveGenerator1245),
      (.mul archiveGenerator0 archiveGenerator1260)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator373))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1245)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1222)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator620)),
      (.mul archiveGenerator1 archiveGenerator1244),
      (.mul archiveGenerator0 archiveGenerator1258),
      (.mul archiveGenerator0 archiveGenerator1257),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator56 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator619)),
      (.mul archiveGenerator1 archiveGenerator1242),
      (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator982))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1244)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator55 archiveGenerator324))))] (
  .cons [archiveGenerator1291,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator618)),
      (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1175))))))] (
  .cons [(.mul archiveGenerator167 archiveGenerator209),
      (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator941)),
      (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator187))] (
  .cons [(.mul archiveGenerator166 archiveGenerator209),
      (.mul archiveGenerator1 (.mul archiveGenerator13 archiveGenerator877))] (
  .cons [archiveGenerator1290,
      (.mul archiveGenerator0 (.mul archiveGenerator102 archiveGenerator324))] (
  .cons [archiveGenerator1289,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator134)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator133))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator418))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1147)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator963)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1169))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator642)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1105)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator715)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator940))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1084)))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator753)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator278))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator962)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator149 archiveGenerator160)),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64))))] (
  .cons [archiveGenerator1288] (
  .cons [archiveGenerator1287] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator59 archiveGenerator491)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1218)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator246))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator491)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator452)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator244))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator225))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator452))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator725))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator224)))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator1033)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator402))))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator806))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator953)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1239))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator952))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1253)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator804))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator804))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator951))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1238)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows206 : BasisRows generators 206 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1299),
      (.mul archiveGenerator0 (.mul archiveGenerator109 archiveGenerator324))] (
  .cons [(.mul archiveGenerator5 archiveGenerator1058),
      (.mul archiveGenerator3 (.mul archiveGenerator84 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1284),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1286))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1282),
      (.mul archiveGenerator1 archiveGenerator1281),
      (.mul archiveGenerator1 (.mul archiveGenerator107 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator18 (.mul archiveGenerator18 archiveGenerator446)))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator95 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1284))] (
  .cons [(.mul archiveGenerator2 archiveGenerator1234),
      (.mul archiveGenerator1 archiveGenerator1278),
      (.mul archiveGenerator1 (.mul archiveGenerator105 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1283)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1281)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator114 archiveGenerator324),
      (.mul archiveGenerator2 archiveGenerator1230),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1279)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1278)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator106 archiveGenerator324)))] (
  .cons [archiveGenerator1310,
      (.mul archiveGenerator13 (.mul archiveGenerator52 archiveGenerator324)),
      (.mul archiveGenerator2 archiveGenerator1227),
      (.mul archiveGenerator1 archiveGenerator1273),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1275)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator103 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator191 archiveGenerator198),
      (.mul archiveGenerator113 archiveGenerator324),
      (.mul archiveGenerator13 (.mul archiveGenerator51 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1272),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1136)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1215)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1273)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1120)))] (
  .cons [archiveGenerator1309,
      (.mul archiveGenerator190 archiveGenerator198),
      (.mul archiveGenerator112 archiveGenerator324),
      (.mul archiveGenerator76 archiveGenerator450),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator324))),
      (.mul archiveGenerator1 archiveGenerator1270),
      (.mul archiveGenerator0 archiveGenerator1297),
      (.mul archiveGenerator0 archiveGenerator1296),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1135)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator92 archiveGenerator367)))] (
  .cons [archiveGenerator1308,
      (.mul archiveGenerator13 archiveGenerator912),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator32 archiveGenerator324))),
      (.mul archiveGenerator1 archiveGenerator1269),
      (.mul archiveGenerator1 archiveGenerator1268),
      (.mul archiveGenerator0 archiveGenerator1295),
      (.mul archiveGenerator0 archiveGenerator1294),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1133)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1132)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1270))] (
  .cons [archiveGenerator1307,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator324)))),
      (.mul archiveGenerator7 archiveGenerator1017),
      (.mul archiveGenerator3 archiveGenerator1157),
      (.mul archiveGenerator2 archiveGenerator1224),
      (.mul archiveGenerator1 archiveGenerator1266),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator988)),
      (.mul archiveGenerator0 archiveGenerator1293),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1131)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1268)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324)))))))] (
  .cons [archiveGenerator1306,
      (.mul archiveGenerator8 (.mul archiveGenerator60 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1156),
      (.mul archiveGenerator2 archiveGenerator1223),
      (.mul archiveGenerator1 archiveGenerator1264),
      (.mul archiveGenerator1 archiveGenerator1263),
      (.mul archiveGenerator0 archiveGenerator1292),
      (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator333)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1129)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1267))] (
  .cons [(.mul archiveGenerator43 archiveGenerator630),
      (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator324))),
      (.mul archiveGenerator2 archiveGenerator1222),
      (.mul archiveGenerator1 archiveGenerator1261),
      (.mul archiveGenerator1 (.mul archiveGenerator189 archiveGenerator190)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1265)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1152),
      (.mul archiveGenerator1 archiveGenerator1260),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1262)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1261)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator31 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1150),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1000)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1260))] (
  .cons [(.mul archiveGenerator43 archiveGenerator628),
      (.mul archiveGenerator1 archiveGenerator1257),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1245)))] (
  .cons [archiveGenerator1305,
      (.mul archiveGenerator9 archiveGenerator945),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1258)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1257))] (
  .cons [(.mul archiveGenerator111 archiveGenerator324),
      (.mul archiveGenerator13 (.mul archiveGenerator101 archiveGenerator209)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator629)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1244)))] (
  .cons [(.mul archiveGenerator110 archiveGenerator324),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator692)),
      (.mul archiveGenerator1 (.mul archiveGenerator187 archiveGenerator187)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator188)))] (
  .cons [archiveGenerator1304,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator628)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator761)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator187)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator901),
      (.mul archiveGenerator9 archiveGenerator941),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator423))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator760))] (
  .cons [(.mul archiveGenerator13 archiveGenerator900),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator690)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator261)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator102 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator42 archiveGenerator627),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator293)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator294)))),
      (.mul archiveGenerator0 archiveGenerator1289)] (
  .cons [archiveGenerator1303,
      (.mul archiveGenerator64 archiveGenerator492),
      (.mul archiveGenerator8 archiveGenerator974),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator209)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator627)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator384)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator963))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator220)))),
      (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator627)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator250)))))] (
  .cons [archiveGenerator1302,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator383))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator248)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator346)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator382))))] (
  .cons [(.mul archiveGenerator138 archiveGenerator260),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator278))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator574)))] (
  .cons [(.mul archiveGenerator64 archiveGenerator491),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator454))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator573))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator113 archiveGenerator149))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator278)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator219)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator206))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator380)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator248)))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator623),
      (.mul archiveGenerator8 archiveGenerator972),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator167)))))),
      (.mul archiveGenerator0 archiveGenerator1287)] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator516)),
      (.mul archiveGenerator8 archiveGenerator971),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator166))))))] (
  .cons [(.mul archiveGenerator138 archiveGenerator257),
      (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator623)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator247))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1218))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator488),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator759)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator245))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator246)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator149))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator491)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator244))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator244))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator572))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator225)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator452))))] (
  .cons [archiveGenerator1301,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator49 archiveGenerator245)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator452)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator452)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator970)] (
  .cons [(.mul archiveGenerator31 archiveGenerator686)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator403)))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator969)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator953))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1239)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator952)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1253)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator804)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator804)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator951)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1300] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows207 : BasisRows generators 207 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator108 archiveGenerator324))] (
  .cons [archiveGenerator1333,
      (.mul archiveGenerator115 archiveGenerator324)] (
  .cons [archiveGenerator1332,
      (.mul archiveGenerator3 archiveGenerator1178),
      (.mul archiveGenerator2 (.mul archiveGenerator101 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1281))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator324))))] (
  .cons [archiveGenerator1331,
      archiveGenerator1330,
      (.mul archiveGenerator92 archiveGenerator415),
      (.mul archiveGenerator1 archiveGenerator1298),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1278))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator106 archiveGenerator324))))] (
  .cons [archiveGenerator1329,
      archiveGenerator1328,
      archiveGenerator1327,
      (.mul archiveGenerator92 archiveGenerator414)] (
  .cons [archiveGenerator1326,
      (.mul archiveGenerator1 archiveGenerator1297),
      (.mul archiveGenerator0 (.mul archiveGenerator113 archiveGenerator324))] (
  .cons [archiveGenerator1325,
      (.mul archiveGenerator107 archiveGenerator352),
      (.mul archiveGenerator2 archiveGenerator1249),
      (.mul archiveGenerator0 (.mul archiveGenerator112 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1296))] (
  .cons [archiveGenerator1324,
      archiveGenerator1323,
      (.mul archiveGenerator7 archiveGenerator1046),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1295)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1133)))] (
  .cons [archiveGenerator1322,
      archiveGenerator1321,
      archiveGenerator1320,
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1017)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1157)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1293)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324))))))))] (
  .cons [archiveGenerator1319,
      (.mul archiveGenerator7 archiveGenerator1042),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1292)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator333))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1267)))] (
  .cons [archiveGenerator1318,
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator630)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1222)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1126)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1245)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1152)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator31 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1150))] (
  .cons [(.mul archiveGenerator188 archiveGenerator201),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator411))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1245))))] (
  .cons [(.mul archiveGenerator187 archiveGenerator201),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator408))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1258))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1257)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1291),
      (.mul archiveGenerator0 (.mul archiveGenerator111 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1244))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator640)),
      (.mul archiveGenerator0 (.mul archiveGenerator110 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator188))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator287))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator705)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator187))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator286))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator188))),
      (.mul archiveGenerator1 archiveGenerator1290)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator79 archiveGenerator188)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator267)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator212)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator779)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator974))] (
  .cons [archiveGenerator1317,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))))),
      (.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator188)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator212))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator627)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator299)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator267)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator627)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator188)))))] (
  .cons [archiveGenerator1316,
      archiveGenerator1315,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator255)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator254))))),
      (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator580))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator404)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator101)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator147)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator173))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator146)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator80)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator637)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator51)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator118))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator516)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator778)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator23))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator623))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1218)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator298)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator137))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator32))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator759))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator246))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator491)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator297)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator138)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator13)))))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator452))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator491))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator138)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator63)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator244)))))] (
  .cons [archiveGenerator1314,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator137)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator20))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator452)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator225)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator40))))))))),
      (.mul archiveGenerator0 archiveGenerator1301)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator225)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator39))))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator1033))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator403)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator171))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator402)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator78)))))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator635),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator117)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator636)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator116)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator636)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator401)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator969))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator635)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator200)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator253)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator252)))))] (
  .cons [archiveGenerator1313,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator777))] (
  .cons [archiveGenerator1312,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator470)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator579)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator578)))] (
  .cons [archiveGenerator1311] (
  .cons [(.mul archiveGenerator17 archiveGenerator852)] (
  .cons [(.mul archiveGenerator8 archiveGenerator996)] (
  .cons [(.mul archiveGenerator8 archiveGenerator995),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator804))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows208 : BasisRows generators 208 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator18 archiveGenerator850)] (
  .cons [(.mul archiveGenerator7 archiveGenerator1058)] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator94 archiveGenerator324))] (
  .cons [archiveGenerator1348,
      (.mul archiveGenerator3 (.mul archiveGenerator93 archiveGenerator324))] (
  .cons [archiveGenerator1347,
      (.mul archiveGenerator7 (.mul archiveGenerator68 archiveGenerator324)),
      (.mul archiveGenerator2 (.mul archiveGenerator2 (.mul archiveGenerator92 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator67 archiveGenerator324)),
      (.mul archiveGenerator3 (.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator324))),
      (.mul archiveGenerator2 archiveGenerator1284)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator107 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator1058))] (
  .cons [archiveGenerator1346,
      archiveGenerator1345,
      (.mul archiveGenerator3 archiveGenerator1200),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator107 archiveGenerator324)))] (
  .cons [archiveGenerator1344,
      archiveGenerator1343,
      archiveGenerator1342,
      (.mul archiveGenerator3 archiveGenerator1198),
      (.mul archiveGenerator3 archiveGenerator1197),
      (.mul archiveGenerator2 (.mul archiveGenerator103 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator115 archiveGenerator324))] (
  .cons [archiveGenerator1341,
      (.mul archiveGenerator3 archiveGenerator1196),
      (.mul archiveGenerator2 archiveGenerator1273),
      (.mul archiveGenerator0 archiveGenerator1332),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1178)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator101 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator324)))))] (
  .cons [archiveGenerator1340,
      (.mul archiveGenerator7 archiveGenerator1057),
      (.mul archiveGenerator2 archiveGenerator1271),
      (.mul archiveGenerator1 archiveGenerator1310),
      (.mul archiveGenerator0 archiveGenerator1331),
      (.mul archiveGenerator0 archiveGenerator1330)] (
  .cons [(.mul archiveGenerator7 archiveGenerator1056),
      (.mul archiveGenerator3 archiveGenerator1192),
      (.mul archiveGenerator3 archiveGenerator1191),
      (.mul archiveGenerator3 archiveGenerator1190),
      (.mul archiveGenerator2 archiveGenerator1270),
      (.mul archiveGenerator0 archiveGenerator1328)] (
  .cons [archiveGenerator1339,
      (.mul archiveGenerator3 archiveGenerator1188),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1056)),
      (.mul archiveGenerator1 (.mul archiveGenerator76 archiveGenerator450)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1270)),
      (.mul archiveGenerator0 archiveGenerator1326),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator113 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1186),
      (.mul archiveGenerator0 archiveGenerator1325),
      (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator352)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1249)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator112 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1323),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1046)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1295)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator933),
      (.mul archiveGenerator2 archiveGenerator1261),
      (.mul archiveGenerator0 archiveGenerator1322),
      (.mul archiveGenerator0 archiveGenerator1320),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1017))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324)))))))))] (
  .cons [archiveGenerator1338,
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1261)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1292))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1267))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1152)),
      (.mul archiveGenerator0 archiveGenerator1318),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator450))),
      (.mul archiveGenerator2 (.mul archiveGenerator188 archiveGenerator189)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator324))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1152))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247)))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator43 archiveGenerator628)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1257)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator31 archiveGenerator324))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1150)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator677)),
      (.mul archiveGenerator7 archiveGenerator1049),
      (.mul archiveGenerator1 archiveGenerator1305),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1245)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator417))),
      (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator832)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1258)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1257))))] (
  .cons [(.mul archiveGenerator180 archiveGenerator209),
      (.mul archiveGenerator1 (.mul archiveGenerator110 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator187 archiveGenerator187))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator111 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1244)))))] (
  .cons [archiveGenerator1337,
      (.mul archiveGenerator1 archiveGenerator1304),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator110 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator188)))))] (
  .cons [(.mul archiveGenerator149 archiveGenerator250),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator187)))))] (
  .cons [(.mul archiveGenerator2 archiveGenerator1256)] (
  .cons [(.mul archiveGenerator9 archiveGenerator963),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator75)))))),
      (.mul archiveGenerator2 archiveGenerator1255),
      (.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator627))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator537)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator67)))))),
      (.mul archiveGenerator1 archiveGenerator1303)] (
  .cons [archiveGenerator1336,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator642))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator715)),
      (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator347)),
      (.mul archiveGenerator0 archiveGenerator1317),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator627))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator784)),
      (.mul archiveGenerator1 archiveGenerator1302),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator627))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator642))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator642)),
      (.mul archiveGenerator0 archiveGenerator1315)] (
  .cons [(.mul archiveGenerator64 archiveGenerator509),
      (.mul archiveGenerator8 archiveGenerator1009),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator491)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator149 archiveGenerator245),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491)))] (
  .cons [archiveGenerator1335] (
  .cons [(.mul archiveGenerator149 archiveGenerator244)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator623)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1218))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator759)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator246)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator491))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator491)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator244))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1314),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator452))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1301))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator636)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator636))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator969)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator635)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1313)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1312)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator852))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator996))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator995)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator804)))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1334] (
  .cons [(.mul archiveGenerator1 archiveGenerator1300)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows209 : BasisRows generators 209 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator850))] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator70 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1058))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator94 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1348)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1347),
      (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator68 archiveGenerator324)))] (
  .cons [archiveGenerator1358,
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1284))] (
  .cons [archiveGenerator1357,
      (.mul archiveGenerator3 archiveGenerator1216),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator107 archiveGenerator324)))] (
  .cons [archiveGenerator1356,
      (.mul archiveGenerator0 archiveGenerator1346),
      (.mul archiveGenerator0 archiveGenerator1345)] (
  .cons [archiveGenerator1355,
      (.mul archiveGenerator3 archiveGenerator1215),
      (.mul archiveGenerator0 archiveGenerator1343),
      (.mul archiveGenerator0 archiveGenerator1342)] (
  .cons [archiveGenerator1354,
      (.mul archiveGenerator118 archiveGenerator324),
      (.mul archiveGenerator1 archiveGenerator1330),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1273)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1332)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator107 archiveGenerator324))))))] (
  .cons [archiveGenerator1353,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator324))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1327),
      (.mul archiveGenerator0 archiveGenerator1340),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1057)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1331)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1330))] (
  .cons [archiveGenerator1352,
      (.mul archiveGenerator76 archiveGenerator485),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator32 archiveGenerator324))),
      (.mul archiveGenerator1 archiveGenerator1326),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1056)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1191)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1328))] (
  .cons [(.mul archiveGenerator9 archiveGenerator992),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator324)))),
      (.mul archiveGenerator7 archiveGenerator1070),
      (.mul archiveGenerator0 archiveGenerator1339),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1188)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1056))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1326))] (
  .cons [(.mul archiveGenerator13 archiveGenerator949),
      (.mul archiveGenerator8 (.mul archiveGenerator63 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1323),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1046)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1186)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator112 archiveGenerator324))))] (
  .cons [archiveGenerator1351,
      (.mul archiveGenerator9 archiveGenerator988),
      (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator20 archiveGenerator324))),
      (.mul archiveGenerator1 archiveGenerator1321),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1323))] (
  .cons [(.mul archiveGenerator95 archiveGenerator417),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator40 archiveGenerator324))),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1042)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1261)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1320)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324))))))))))] (
  .cons [(.mul archiveGenerator188 archiveGenerator209),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator39 archiveGenerator324))),
      (.mul archiveGenerator7 archiveGenerator1065),
      (.mul archiveGenerator0 archiveGenerator1338),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1267)))))] (
  .cons [(.mul archiveGenerator187 archiveGenerator209),
      (.mul archiveGenerator13 archiveGenerator946),
      (.mul archiveGenerator4 archiveGenerator1152),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1064)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263)))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator945),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247))))))] (
  .cons [(.mul archiveGenerator117 archiveGenerator324)] (
  .cons [(.mul archiveGenerator116 archiveGenerator324),
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator692)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1049)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1245))))))] (
  .cons [archiveGenerator1350,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator181)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator761)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1258)))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator941),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator423))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator798)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator111 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator690)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator261)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator188))))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator655),
      (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator293)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator294)))),
      (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator250)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator187))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1035),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator318)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator518),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator292))),
      (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator655)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator423))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator517),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator797)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator261)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator209))))),
      (.mul archiveGenerator0 archiveGenerator1336)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator248)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator346)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator209))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1317))] (
  .cons [(.mul archiveGenerator138 archiveGenerator278),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator602))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator420))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator516),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator599))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator292)))),
      (.mul archiveGenerator1 archiveGenerator1315)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator598))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator219))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1315))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator149)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator248))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator260))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator509)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator491)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator796)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator167)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator260))),
      (.mul archiveGenerator8 archiveGenerator1034),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator180)))))),
      (.mul archiveGenerator0 archiveGenerator1335)] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator138 archiveGenerator149)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator491))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator259))))),
      (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator244))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator244)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator491))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator258)))))] (
  .cons [archiveGenerator1349,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator206)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator257)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator597))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator246))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator491)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1033),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator596)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator488))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator244)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator595))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator452)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1032),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1301)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1031)] (
  .cons [(.mul archiveGenerator17 archiveGenerator871)] (
  .cons [(.mul archiveGenerator8 archiveGenerator1030),
      (.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator635))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator636))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator635))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1312),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1313))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1312))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator996)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator995))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator804))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1334)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows210 : BasisRows generators 210 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator850))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1058)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator850)))] (
  .cons [(.mul archiveGenerator122 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1058)))] (
  .cons [(.mul archiveGenerator121 archiveGenerator324),
      (.mul archiveGenerator1 archiveGenerator1348)] (
  .cons [(.mul archiveGenerator120 archiveGenerator324),
      (.mul archiveGenerator3 archiveGenerator1237),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1348))] (
  .cons [archiveGenerator1380,
      (.mul archiveGenerator3 archiveGenerator1236),
      (.mul archiveGenerator3 archiveGenerator1235),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator68 archiveGenerator324))))] (
  .cons [archiveGenerator1379,
      (.mul archiveGenerator8 (.mul archiveGenerator68 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1234),
      (.mul archiveGenerator3 archiveGenerator1233),
      (.mul archiveGenerator0 archiveGenerator1358)] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator72 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1232),
      (.mul archiveGenerator3 archiveGenerator1231),
      (.mul archiveGenerator3 archiveGenerator1230),
      (.mul archiveGenerator1 archiveGenerator1346),
      (.mul archiveGenerator1 archiveGenerator1345),
      (.mul archiveGenerator0 archiveGenerator1357),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1216))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1229),
      (.mul archiveGenerator3 archiveGenerator1228),
      (.mul archiveGenerator3 archiveGenerator1227),
      (.mul archiveGenerator2 (.mul archiveGenerator114 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1344),
      (.mul archiveGenerator1 archiveGenerator1343),
      (.mul archiveGenerator1 archiveGenerator1342),
      (.mul archiveGenerator0 archiveGenerator1356),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1346)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1345))] (
  .cons [archiveGenerator1378,
      (.mul archiveGenerator119 archiveGenerator324),
      (.mul archiveGenerator7 archiveGenerator1091),
      (.mul archiveGenerator3 archiveGenerator1226),
      (.mul archiveGenerator1 archiveGenerator1341),
      (.mul archiveGenerator0 archiveGenerator1355),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1215)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1342))] (
  .cons [archiveGenerator1377,
      archiveGenerator1376,
      (.mul archiveGenerator43 archiveGenerator674),
      (.mul archiveGenerator7 archiveGenerator1089),
      (.mul archiveGenerator3 archiveGenerator1225),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1091)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1057)),
      (.mul archiveGenerator0 archiveGenerator1354),
      (.mul archiveGenerator0 (.mul archiveGenerator118 archiveGenerator324))] (
  .cons [archiveGenerator1375,
      archiveGenerator1374,
      archiveGenerator1373,
      (.mul archiveGenerator43 archiveGenerator673),
      (.mul archiveGenerator2 archiveGenerator1309),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1192)),
      (.mul archiveGenerator0 archiveGenerator1353),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1340)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1057)))] (
  .cons [(.mul archiveGenerator190 archiveGenerator213),
      (.mul archiveGenerator8 archiveGenerator1057),
      (.mul archiveGenerator7 archiveGenerator1087),
      (.mul archiveGenerator3 archiveGenerator1224),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1088)),
      (.mul archiveGenerator1 archiveGenerator1339),
      (.mul archiveGenerator0 archiveGenerator1352),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1056)))] (
  .cons [archiveGenerator1372,
      (.mul archiveGenerator3 archiveGenerator1223),
      (.mul archiveGenerator2 archiveGenerator1307),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1339)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1326)))] (
  .cons [(.mul archiveGenerator189 archiveGenerator213),
      (.mul archiveGenerator3 archiveGenerator1222)] (
  .cons [archiveGenerator1371,
      (.mul archiveGenerator188 archiveGenerator213),
      (.mul archiveGenerator0 archiveGenerator1351)] (
  .cons [archiveGenerator1370,
      (.mul archiveGenerator9 archiveGenerator1002),
      (.mul archiveGenerator1 archiveGenerator1338),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324)))))))))))] (
  .cons [(.mul archiveGenerator189 archiveGenerator212),
      (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1338))] (
  .cons [(.mul archiveGenerator188 archiveGenerator212),
      (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263))))))] (
  .cons [(.mul archiveGenerator187 archiveGenerator212),
      (.mul archiveGenerator13 archiveGenerator959),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247)))))))] (
  .cons [archiveGenerator1369,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator474))),
      (.mul archiveGenerator0 (.mul archiveGenerator117 archiveGenerator324))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator190)))),
      (.mul archiveGenerator0 (.mul archiveGenerator116 archiveGenerator324))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator705)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator110 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1258))))))] (
  .cons [archiveGenerator1368,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator189)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator111 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188)))),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator472))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator201))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator188)))))))] (
  .cons [archiveGenerator1367,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator303))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator267)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator610)))] (
  .cons [archiveGenerator1366,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator813)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1035))] (
  .cons [archiveGenerator1365,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator812)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator655)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator327)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator188))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator797)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator33))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator72))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator267))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator347)))] (
  .cons [archiveGenerator1364,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator188)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1317)))] (
  .cons [(.mul archiveGenerator64 archiveGenerator529),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator187)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator278))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator435)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator516))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator434)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator101))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator491))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1315)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator299)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator186)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator509))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator64))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator80))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator808)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator127))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator149 archiveGenerator244)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1335))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator138))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator72)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator491)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator244)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator225))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator113)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator32))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator224))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator147)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13))))))))))] (
  .cons [archiveGenerator1363,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator185)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator42)))))))))] (
  .cons [archiveGenerator1362,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator184)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator23)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator238)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1033))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator298)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator433)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator125)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator432)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator50))))))))] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator556)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator663)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator806)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator265)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator805)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator111))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator183))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator182))))))] (
  .cons [archiveGenerator1361,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator607)))] (
  .cons [archiveGenerator1360,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator296))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator296))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator431)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1313)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1048),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1312)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator554))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator804))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator803))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253))))))] (
  .cons [archiveGenerator1359] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1334))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows211 : BasisRows generators 211 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 (.mul archiveGenerator70 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator850))))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 (.mul archiveGenerator76 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator122 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1058))))] (
  .cons [(.mul archiveGenerator4 (.mul archiveGenerator92 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator121 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator120 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1380)] (
  .cons [archiveGenerator1394,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator68 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1358))] (
  .cons [archiveGenerator1393,
      archiveGenerator1392,
      (.mul archiveGenerator124 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator72 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1230)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1357))] (
  .cons [archiveGenerator1391,
      archiveGenerator1390,
      (.mul archiveGenerator7 archiveGenerator1099),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1227)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1356)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1346))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1345)))] (
  .cons [archiveGenerator1389,
      (.mul archiveGenerator7 archiveGenerator1098),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1091)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1226)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1355)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1215))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1342)))] (
  .cons [archiveGenerator1388,
      archiveGenerator1387,
      (.mul archiveGenerator0 archiveGenerator1377),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator674)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1225)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1091))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1354)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator118 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator76 archiveGenerator485)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1326)),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator673)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1353)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1057))))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1246),
      (.mul archiveGenerator2 archiveGenerator1323),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1057)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1224)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1088)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1096),
      (.mul archiveGenerator2 archiveGenerator1320),
      (.mul archiveGenerator0 archiveGenerator1372),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1223)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1339)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator75 archiveGenerator288)),
      (.mul archiveGenerator3 archiveGenerator1245),
      (.mul archiveGenerator2 archiveGenerator1319),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1222))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator682)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator681)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1351))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator450))),
      (.mul archiveGenerator0 archiveGenerator1370),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator90 archiveGenerator324))))))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator679)),
      (.mul archiveGenerator1 (.mul archiveGenerator187 archiveGenerator209)),
      (.mul archiveGenerator1 (.mul archiveGenerator4 archiveGenerator1152)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1338)))] (
  .cons [archiveGenerator1386,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator677)),
      (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263)))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator67 archiveGenerator286)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247))))))))] (
  .cons [(.mul archiveGenerator194 archiveGenerator209),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator117 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator48 archiveGenerator627),
      (.mul archiveGenerator8 archiveGenerator1062),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator116 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator149 archiveGenerator261),
      (.mul archiveGenerator123 archiveGenerator324)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator76)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator111 archiveGenerator324))))))] (
  .cons [archiveGenerator1385,
      (.mul archiveGenerator13 archiveGenerator963),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator75))))))] (
  .cons [archiveGenerator1384,
      archiveGenerator1383] (
  .cons [archiveGenerator1382,
      (.mul archiveGenerator0 archiveGenerator1366)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator715)),
      (.mul archiveGenerator0 archiveGenerator1365),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator655))))] (
  .cons [(.mul archiveGenerator149 archiveGenerator260),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator784))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator821))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator820))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1061),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator529)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator278)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1060),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator516)))] (
  .cons [archiveGenerator1381,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1315))))] (
  .cons [(.mul archiveGenerator149 archiveGenerator257),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator509)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1335)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator491))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator244))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1349),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator491)))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1362)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1033)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator663)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator806)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator805)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1361)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1360)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1312))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1313))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1312))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator804)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator803)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253)))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1359)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows212 : BasisRows generators 212 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator132 archiveGenerator324)] (
  .cons [(.mul archiveGenerator131 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator850)))] (
  .cons [archiveGenerator1424,
      archiveGenerator1423,
      (.mul archiveGenerator130 archiveGenerator324)] (
  .cons [archiveGenerator1422,
      (.mul archiveGenerator129 archiveGenerator324),
      (.mul archiveGenerator128 archiveGenerator324),
      (.mul archiveGenerator3 archiveGenerator1286),
      (.mul archiveGenerator1 (.mul archiveGenerator122 archiveGenerator324))] (
  .cons [archiveGenerator1421,
      archiveGenerator1420,
      (.mul archiveGenerator3 archiveGenerator1284),
      (.mul archiveGenerator1 (.mul archiveGenerator121 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1348)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator122 archiveGenerator324)))] (
  .cons [archiveGenerator1419,
      archiveGenerator1418,
      archiveGenerator1417,
      (.mul archiveGenerator3 archiveGenerator1282),
      (.mul archiveGenerator3 archiveGenerator1281),
      (.mul archiveGenerator3 (.mul archiveGenerator107 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator121 archiveGenerator324)))] (
  .cons [archiveGenerator1416,
      archiveGenerator1415,
      archiveGenerator1414,
      (.mul archiveGenerator3 archiveGenerator1279),
      (.mul archiveGenerator3 archiveGenerator1278),
      (.mul archiveGenerator1 archiveGenerator1380),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator120 archiveGenerator324)))] (
  .cons [archiveGenerator1413,
      (.mul archiveGenerator7 archiveGenerator1120),
      (.mul archiveGenerator3 archiveGenerator1276),
      (.mul archiveGenerator2 archiveGenerator1345),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1380))] (
  .cons [archiveGenerator1412,
      archiveGenerator1411,
      (.mul archiveGenerator7 archiveGenerator1118),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1120)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1346)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator68 archiveGenerator324))))] (
  .cons [archiveGenerator1410,
      archiveGenerator1409,
      (.mul archiveGenerator127 archiveGenerator324),
      (.mul archiveGenerator126 archiveGenerator324),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator24 archiveGenerator324))),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1118)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1343)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1342)),
      (.mul archiveGenerator0 archiveGenerator1393),
      (.mul archiveGenerator0 archiveGenerator1392)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator324))),
      (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator119 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1391),
      (.mul archiveGenerator0 archiveGenerator1390),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1099)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1356))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1346))))] (
  .cons [(.mul archiveGenerator68 archiveGenerator544),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator32 archiveGenerator324))),
      (.mul archiveGenerator1 archiveGenerator1376),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1098)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1091))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1342))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator992),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator324)))),
      (.mul archiveGenerator1 archiveGenerator1374),
      (.mul archiveGenerator0 archiveGenerator1387),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1377))] (
  .cons [(.mul archiveGenerator67 archiveGenerator543),
      (.mul archiveGenerator13 archiveGenerator990),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator324))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1339)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1353)))] (
  .cons [archiveGenerator1408,
      (.mul archiveGenerator13 archiveGenerator988),
      (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator23 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1261),
      (.mul archiveGenerator3 (.mul archiveGenerator189 archiveGenerator190)),
      (.mul archiveGenerator1 archiveGenerator1372),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1224)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator324)))),
      (.mul archiveGenerator3 archiveGenerator1260),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1320)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1372)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1223)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator324)))),
      (.mul archiveGenerator7 archiveGenerator1107),
      (.mul archiveGenerator2 archiveGenerator1338),
      (.mul archiveGenerator1 archiveGenerator1371),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1245))] (
  .cons [(.mul archiveGenerator201 archiveGenerator209),
      (.mul archiveGenerator125 archiveGenerator324),
      (.mul archiveGenerator3 archiveGenerator1257),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1338)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1351)))] (
  .cons [archiveGenerator1407,
      (.mul archiveGenerator17 (.mul archiveGenerator50 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1370))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator50 archiveGenerator324)),
      (.mul archiveGenerator9 archiveGenerator1038),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator209)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1338))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator692)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator691)),
      (.mul archiveGenerator8 (.mul archiveGenerator71 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1386),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator209)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263))))))))] (
  .cons [archiveGenerator1406,
      archiveGenerator1405,
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator761)),
      (.mul archiveGenerator1 archiveGenerator1369),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247)))))))))] (
  .cons [archiveGenerator1404,
      (.mul archiveGenerator13 archiveGenerator979),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator209)))] (
  .cons [archiveGenerator1403,
      (.mul archiveGenerator13 archiveGenerator978),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator690)),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator261)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator79 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator116 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator975),
      (.mul archiveGenerator8 archiveGenerator1079),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator294)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator834)),
      (.mul archiveGenerator1 archiveGenerator1368)] (
  .cons [archiveGenerator1402,
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator348)),
      (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator627)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209))))),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1256))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator209)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator832)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator423)))),
      (.mul archiveGenerator1 archiveGenerator1367),
      (.mul archiveGenerator0 archiveGenerator1385)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator347)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator627))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator261))))),
      (.mul archiveGenerator0 archiveGenerator1383)] (
  .cons [archiveGenerator1401,
      (.mul archiveGenerator64 archiveGenerator549),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator150))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator280))))),
      (.mul archiveGenerator0 archiveGenerator1382),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1366))] (
  .cons [(.mul archiveGenerator17 archiveGenerator897),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator248)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator346)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator279))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1365))] (
  .cons [(.mul archiveGenerator16 archiveGenerator897),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator625))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator420)))),
      (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator260))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator260)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator455))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator624))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator454))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator160)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator248))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator278)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator516)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator831)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator167)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator516))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator380))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator830)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator194)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1315)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator113 archiveGenerator244)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator516))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator193)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator509))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator343)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator623))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator277))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator149 archiveGenerator244))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491)))))))] (
  .cons [archiveGenerator1400,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator149)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1335))))] (
  .cons [archiveGenerator1399,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator149)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator244)))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator896),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator453))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1076),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator31 archiveGenerator245)))),
      (.mul archiveGenerator1 archiveGenerator1363)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator244))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator452))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator829)),
      (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator402))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator686))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator685))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator685))] (
  .cons [archiveGenerator1398,
      archiveGenerator1397] (
  .cons [archiveGenerator1396] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator806))))] (
  .cons [archiveGenerator1395] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1361))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1360))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1313)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1312)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator804))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator803))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1359),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1359))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows213 : BasisRows generators 213 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator132 archiveGenerator324))] (
  .cons [archiveGenerator1437,
      (.mul archiveGenerator0 (.mul archiveGenerator131 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1423),
      (.mul archiveGenerator0 (.mul archiveGenerator130 archiveGenerator324))] (
  .cons [(.mul archiveGenerator134 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator129 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator128 archiveGenerator324))] (
  .cons [(.mul archiveGenerator133 archiveGenerator324),
      (.mul archiveGenerator0 archiveGenerator1420),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator122 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1418),
      (.mul archiveGenerator0 archiveGenerator1417),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1281)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator107 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1137),
      (.mul archiveGenerator0 archiveGenerator1416),
      (.mul archiveGenerator0 archiveGenerator1414),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1279)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator120 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1120)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1276)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1345)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1380)))] (
  .cons [archiveGenerator1436,
      (.mul archiveGenerator1 archiveGenerator1392),
      (.mul archiveGenerator1 (.mul archiveGenerator124 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1412),
      (.mul archiveGenerator0 archiveGenerator1411),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1118)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1120)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1134),
      (.mul archiveGenerator3 archiveGenerator1296),
      (.mul archiveGenerator2 archiveGenerator1354),
      (.mul archiveGenerator1 archiveGenerator1391),
      (.mul archiveGenerator0 archiveGenerator1410),
      (.mul archiveGenerator0 archiveGenerator1409),
      (.mul archiveGenerator0 (.mul archiveGenerator127 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator126 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1118))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1392))] (
  .cons [archiveGenerator1435,
      (.mul archiveGenerator3 archiveGenerator1294),
      (.mul archiveGenerator2 archiveGenerator1353),
      (.mul archiveGenerator1 archiveGenerator1389),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1390)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1099))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1346)))))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1293),
      (.mul archiveGenerator2 archiveGenerator1352),
      (.mul archiveGenerator1 archiveGenerator1388),
      (.mul archiveGenerator1 archiveGenerator1387),
      (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator544)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1098)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1128),
      (.mul archiveGenerator3 archiveGenerator1292),
      (.mul archiveGenerator3 (.mul archiveGenerator107 archiveGenerator333)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1377)))] (
  .cons [archiveGenerator1434,
      (.mul archiveGenerator7 archiveGenerator1127),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator543))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1004),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1261))] (
  .cons [archiveGenerator1433,
      (.mul archiveGenerator13 archiveGenerator1002),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1260))] (
  .cons [archiveGenerator1432,
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1338)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1245)))] (
  .cons [archiveGenerator1431,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1257)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1351))))] (
  .cons [archiveGenerator1430,
      (.mul archiveGenerator201 archiveGenerator212),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator476))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator187 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator50 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1370)))] (
  .cons [archiveGenerator1429,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator474))),
      (.mul archiveGenerator1 archiveGenerator1386),
      (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator50 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator209))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1338)))))] (
  .cons [archiveGenerator1428,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator71 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator209))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263)))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator705)),
      (.mul archiveGenerator0 archiveGenerator1405),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1247))))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator473))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator188))),
      (.mul archiveGenerator1 (.mul archiveGenerator48 archiveGenerator627)),
      (.mul archiveGenerator0 archiveGenerator1404)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator472))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator212))),
      (.mul archiveGenerator1 (.mul archiveGenerator123 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1403)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator267)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator640)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator638))),
      (.mul archiveGenerator1 archiveGenerator1385),
      (.mul archiveGenerator0 archiveGenerator1402)] (
  .cons [archiveGenerator1427,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator854)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212))))),
      (.mul archiveGenerator1 archiveGenerator1383),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator832))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1385))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator188))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator188))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator627)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1383))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator187))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator267))))),
      (.mul archiveGenerator0 archiveGenerator1401),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1366)))] (
  .cons [(.mul archiveGenerator64 archiveGenerator558),
      (.mul archiveGenerator8 archiveGenerator1094),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator188)))))),
      (.mul archiveGenerator1 (.mul archiveGenerator149 archiveGenerator260)),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator897))] (
  .cons [(.mul archiveGenerator64 archiveGenerator557),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator201)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator897)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator138)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator435)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator471)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator113))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator80)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator112))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator80)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator529))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1315))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator637))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator79)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator509)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator238))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator154)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator32))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator237))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator154)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1335)))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator918),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator46))))))))),
      (.mul archiveGenerator0 archiveGenerator1399),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator244))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1093),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator45))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator896))] (
  .cons [(.mul archiveGenerator64 archiveGenerator556),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator224)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1076))] (
  .cons [(.mul archiveGenerator64 archiveGenerator555),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator225))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator225))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator136)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator224))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator56))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator403))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator78))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator403))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator77))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator636))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator283)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator635))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator153)))))),
      (.mul archiveGenerator0 archiveGenerator1397)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator200)))))),
      (.mul archiveGenerator0 archiveGenerator1396)] (
  .cons [(.mul archiveGenerator17 archiveGenerator917),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator199))))))] (
  .cons [(.mul archiveGenerator16 archiveGenerator917),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator634))),
      (.mul archiveGenerator0 archiveGenerator1395)] (
  .cons [(.mul archiveGenerator16 archiveGenerator916),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator326))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator470))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator469))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1092),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1360)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator701))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator852)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1313))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator851)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1312))))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1426] (
  .cons [archiveGenerator1425] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253)))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows214 : BasisRows generators 214 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator132 archiveGenerator324)))] (
  .cons [archiveGenerator1466,
      (.mul archiveGenerator2 (.mul archiveGenerator122 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1437)] (
  .cons [archiveGenerator1465,
      archiveGenerator1464,
      (.mul archiveGenerator1 archiveGenerator1422),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator122 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator130 archiveGenerator324)))] (
  .cons [archiveGenerator1463,
      archiveGenerator1462,
      archiveGenerator1461,
      (.mul archiveGenerator1 archiveGenerator1420),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator129 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator128 archiveGenerator324)))] (
  .cons [archiveGenerator1460,
      (.mul archiveGenerator7 archiveGenerator1164),
      (.mul archiveGenerator2 archiveGenerator1380),
      (.mul archiveGenerator1 archiveGenerator1419),
      (.mul archiveGenerator1 archiveGenerator1418),
      (.mul archiveGenerator0 (.mul archiveGenerator133 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1420))] (
  .cons [archiveGenerator1459,
      archiveGenerator1458,
      (.mul archiveGenerator7 archiveGenerator1162),
      (.mul archiveGenerator1 archiveGenerator1414),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1380)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1418)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1417)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator107 archiveGenerator324))))] (
  .cons [archiveGenerator1457,
      archiveGenerator1456,
      archiveGenerator1455,
      archiveGenerator1454,
      (.mul archiveGenerator7 archiveGenerator1161),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1416)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1414)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator120 archiveGenerator324)))))] (
  .cons [archiveGenerator1453,
      archiveGenerator1452,
      (.mul archiveGenerator7 archiveGenerator1160),
      (.mul archiveGenerator1 archiveGenerator1412),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1118)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1120)))] (
  .cons [archiveGenerator1451,
      archiveGenerator1450,
      (.mul archiveGenerator43 archiveGenerator719),
      (.mul archiveGenerator7 archiveGenerator1159),
      (.mul archiveGenerator1 archiveGenerator1409),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1411)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1118)))] (
  .cons [archiveGenerator1449,
      (.mul archiveGenerator7 archiveGenerator1158),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1296)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1410)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator127 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator126 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1392)))] (
  .cons [archiveGenerator1448,
      archiveGenerator1447,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1294)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1353)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1390)))] (
  .cons [archiveGenerator1446,
      (.mul archiveGenerator7 archiveGenerator1156),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1157)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator544)))] (
  .cons [archiveGenerator1445,
      (.mul archiveGenerator7 archiveGenerator1154),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1292))] (
  .cons [(.mul archiveGenerator209 archiveGenerator209),
      (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator288)),
      (.mul archiveGenerator7 archiveGenerator1152),
      (.mul archiveGenerator0 archiveGenerator1434)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1261)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator1002)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1260)))] (
  .cons [archiveGenerator1444,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator373))),
      (.mul archiveGenerator1 (.mul archiveGenerator125 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1257)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1245))))] (
  .cons [archiveGenerator1443,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1257))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1351)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator50 archiveGenerator324))))] (
  .cons [archiveGenerator1442,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator335))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator50 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator209))))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator1062),
      (.mul archiveGenerator0 archiveGenerator1428),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator71 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator209)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263))))))))))] (
  .cons [archiveGenerator1441,
      (.mul archiveGenerator8 archiveGenerator1104)] (
  .cons [(.mul archiveGenerator149 archiveGenerator280),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1404))] (
  .cons [(.mul archiveGenerator149 archiveGenerator279),
      (.mul archiveGenerator135 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1403))] (
  .cons [archiveGenerator1440,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator95)))))),
      (.mul archiveGenerator1 archiveGenerator1402)] (
  .cons [archiveGenerator1439,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator716)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator83)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1402))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator715)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator832)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1385)))] (
  .cons [(.mul archiveGenerator149 archiveGenerator278),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator784)),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator549)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1383)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator864)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1401)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1366))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator642))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator558)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator897)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator863)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator897))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1102),
      (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator138))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator16 archiveGenerator927),
      (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator149 archiveGenerator149))] (
  .cons [archiveGenerator1438] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator509))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator260)))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator491)))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1335))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator244)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1093)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator896)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator556)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1076)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator555))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator402)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1397),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator636))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator635)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1395),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator917))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator917)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1395))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator916))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1313)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1312)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1426)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1425)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1359))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows215 : BasisRows generators 215 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator122 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator139 archiveGenerator324),
      (.mul archiveGenerator0 archiveGenerator1464)] (
  .cons [archiveGenerator1479,
      archiveGenerator1478,
      (.mul archiveGenerator0 archiveGenerator1461),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator128 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1178),
      (.mul archiveGenerator0 archiveGenerator1460),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1380)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1420)))] (
  .cons [archiveGenerator1477,
      (.mul archiveGenerator3 archiveGenerator1332),
      (.mul archiveGenerator0 archiveGenerator1459),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1418))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1417)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1331),
      (.mul archiveGenerator3 archiveGenerator1330),
      (.mul archiveGenerator0 archiveGenerator1456),
      (.mul archiveGenerator0 archiveGenerator1455),
      (.mul archiveGenerator0 archiveGenerator1454),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1414)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator79 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1328),
      (.mul archiveGenerator1 archiveGenerator1436),
      (.mul archiveGenerator0 archiveGenerator1453),
      (.mul archiveGenerator0 archiveGenerator1452),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1160))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator32 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1326),
      (.mul archiveGenerator0 archiveGenerator1450),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator719)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1159))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator324)))),
      (.mul archiveGenerator1 archiveGenerator1435),
      (.mul archiveGenerator0 archiveGenerator1449),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1158))] (
  .cons [(.mul archiveGenerator138 archiveGenerator324),
      (.mul archiveGenerator9 archiveGenerator1089),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator46 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1323),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1387)),
      (.mul archiveGenerator0 archiveGenerator1447)] (
  .cons [(.mul archiveGenerator137 archiveGenerator324),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator734)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator45 archiveGenerator324))),
      (.mul archiveGenerator7 archiveGenerator1175),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1128)),
      (.mul archiveGenerator0 archiveGenerator1446),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1157)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator1087),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator324)))),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1127)),
      (.mul archiveGenerator0 archiveGenerator1445),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1154)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1292)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1045),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator19 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator209 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1152))] (
  .cons [(.mul archiveGenerator209 archiveGenerator212),
      (.mul archiveGenerator136 archiveGenerator324),
      (.mul archiveGenerator1 archiveGenerator1433)] (
  .cons [archiveGenerator1476,
      (.mul archiveGenerator17 (.mul archiveGenerator56 archiveGenerator324)),
      (.mul archiveGenerator13 archiveGenerator1041)] (
  .cons [(.mul archiveGenerator13 archiveGenerator1038),
      (.mul archiveGenerator8 (.mul archiveGenerator78 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1444)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator77 archiveGenerator324)),
      (.mul archiveGenerator1 archiveGenerator1430),
      (.mul archiveGenerator0 archiveGenerator1443),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1351))))))] (
  .cons [archiveGenerator1475,
      archiveGenerator1474,
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator761)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1386)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator50 archiveGenerator324)))))] (
  .cons [archiveGenerator1473,
      (.mul archiveGenerator23 archiveGenerator877),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator262)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator209))),
      (.mul archiveGenerator0 archiveGenerator1442),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator209)))))))] (
  .cons [(.mul archiveGenerator23 archiveGenerator876),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator261)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator89 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1263)))))))))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator1079),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator294)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator878)),
      (.mul archiveGenerator0 archiveGenerator1441)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator655)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator250))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator383)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator874)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator423))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator346))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator382)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator655))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator261))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1385))] (
  .cons [(.mul archiveGenerator64 archiveGenerator574),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator294))))),
      (.mul archiveGenerator0 archiveGenerator1439),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1402)))] (
  .cons [(.mul archiveGenerator64 archiveGenerator573),
      (.mul archiveGenerator17 archiveGenerator940),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator346)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator209)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1385))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator8 (.mul archiveGenerator113 archiveGenerator260)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator293))))),
      (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator278)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1383))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator380)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator492)))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator149 archiveGenerator260))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1401))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1366)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator347)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator292))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator558))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator897))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator347)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator248))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator291))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator260)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator60 archiveGenerator260))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator653))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator167)))))),
      (.mul archiveGenerator1 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator245))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator260)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator194)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator149))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator260)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator208))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator244))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator491)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator207))))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator725),
      (.mul archiveGenerator8 archiveGenerator1121),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator160))))))] (
  .cons [archiveGenerator1472,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator206))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator725)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator490))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator725)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator489))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator343))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator488))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator873)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator556)))] (
  .cons [archiveGenerator1471,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator872))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator722))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator871))] (
  .cons [archiveGenerator1470] (
  .cons [archiveGenerator1469] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator636)))))] (
  .cons [archiveGenerator1468,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator917)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator917))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1395)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator916)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1313))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1312))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1426))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1425))] (
  .cons [archiveGenerator1467] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1253)))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows216 : BasisRows generators 216 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator143 archiveGenerator324)] (
  .cons [(.mul archiveGenerator142 archiveGenerator324)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator132 archiveGenerator324))] (
  .cons [archiveGenerator1498,
      (.mul archiveGenerator7 (.mul archiveGenerator92 archiveGenerator324)),
      (.mul archiveGenerator2 (.mul archiveGenerator131 archiveGenerator324))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1348),
      (.mul archiveGenerator2 archiveGenerator1424),
      (.mul archiveGenerator2 (.mul archiveGenerator130 archiveGenerator324))] (
  .cons [archiveGenerator1497,
      (.mul archiveGenerator2 archiveGenerator1422),
      (.mul archiveGenerator1 archiveGenerator1466)] (
  .cons [(.mul archiveGenerator2 archiveGenerator1421),
      (.mul archiveGenerator1 archiveGenerator1465),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator122 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator141 archiveGenerator324),
      (.mul archiveGenerator9 (.mul archiveGenerator75 archiveGenerator324)),
      (.mul archiveGenerator2 archiveGenerator1418),
      (.mul archiveGenerator2 archiveGenerator1417),
      (.mul archiveGenerator1 archiveGenerator1462)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator67 archiveGenerator324)),
      (.mul archiveGenerator3 archiveGenerator1345),
      (.mul archiveGenerator2 archiveGenerator1415),
      (.mul archiveGenerator2 archiveGenerator1414),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1418)),
      (.mul archiveGenerator0 archiveGenerator1479),
      (.mul archiveGenerator0 archiveGenerator1478),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1461)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator128 archiveGenerator324)))))] (
  .cons [archiveGenerator1496,
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1197)),
      (.mul archiveGenerator1 archiveGenerator1458),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1414)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1178)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1380))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1420))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1455),
      (.mul archiveGenerator1 archiveGenerator1454),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1332)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1459)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1418)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1417))))] (
  .cons [archiveGenerator1495,
      (.mul archiveGenerator2 (.mul archiveGenerator126 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1331)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1454)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1414))))] (
  .cons [archiveGenerator1494,
      archiveGenerator1493,
      (.mul archiveGenerator1 archiveGenerator1450),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator79 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1328)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1453)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1160)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1057),
      (.mul archiveGenerator1 archiveGenerator1449),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1158)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1326)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator719))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1159)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1185),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1186)),
      (.mul archiveGenerator1 archiveGenerator1448),
      (.mul archiveGenerator1 archiveGenerator1447),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1449))] (
  .cons [archiveGenerator1492,
      (.mul archiveGenerator1 archiveGenerator1446),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1156)),
      (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1447))] (
  .cons [archiveGenerator1491,
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1154)),
      (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1175)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1446))] (
  .cons [(.mul archiveGenerator212 archiveGenerator213),
      (.mul archiveGenerator1 (.mul archiveGenerator209 archiveGenerator209)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1152)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1445)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1154)))] (
  .cons [archiveGenerator1490,
      (.mul archiveGenerator9 archiveGenerator1096),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator209 archiveGenerator209)))] (
  .cons [archiveGenerator1489,
      (.mul archiveGenerator13 archiveGenerator1052)] (
  .cons [archiveGenerator1488,
      archiveGenerator1487,
      (.mul archiveGenerator212 archiveGenerator212),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator56 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator209 archiveGenerator215),
      (.mul archiveGenerator13 archiveGenerator1050),
      (.mul archiveGenerator8 archiveGenerator1148),
      (.mul archiveGenerator1 archiveGenerator1443),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator78 archiveGenerator324)))] (
  .cons [archiveGenerator1486,
      archiveGenerator1485,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator288)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator77 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1443))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator213)))),
      (.mul archiveGenerator1 archiveGenerator1442),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator50 archiveGenerator324))))))] (
  .cons [archiveGenerator1484,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1442))] (
  .cons [archiveGenerator1483,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator268)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator212))),
      (.mul archiveGenerator1 archiveGenerator1441)] (
  .cons [(.mul archiveGenerator140 archiveGenerator324),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator267)))),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator286)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator640))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1441))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator266)))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator668))),
      (.mul archiveGenerator1 (.mul archiveGenerator135 archiveGenerator324))] (
  .cons [archiveGenerator1482,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator667)))] (
  .cons [archiveGenerator1481,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator255))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator254))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator267)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator24))))))),
      (.mul archiveGenerator8 archiveGenerator1145),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator188)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator573)),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator940))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator404)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator212)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator113 archiveGenerator260))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1383)))))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator147)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator435)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator380))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1401))))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator146)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator499)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator558)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator897)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator299))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator80))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator260))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator64)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator89))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator138)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator665))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator80)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator664))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator89)))))))),
      (.mul archiveGenerator1 archiveGenerator1438)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator138)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator162)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator137)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator113))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1144),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator147))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator51)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator225)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator146))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator23)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator725)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator403)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator185))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator22)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator725)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator402)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator238))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator8)))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator298))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator88))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator297))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator17)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator433))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50))))))))),
      (.mul archiveGenerator0 archiveGenerator1471)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator556))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator663))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator211))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator662))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator111)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator111))))))),
      (.mul archiveGenerator0 archiveGenerator1469)] (
  .cons [(.mul archiveGenerator17 archiveGenerator953),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator145)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1142),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator498)))),
      (.mul archiveGenerator0 archiveGenerator1468),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1141),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator183))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1395)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator296))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator917))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator295))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1395))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator886))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator554)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator554)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator661)))] (
  .cons [archiveGenerator1480] (
  .cons [] (
  .cons [(.mul archiveGenerator8 archiveGenerator1140)] (
  .cons [(.mul archiveGenerator8 archiveGenerator1139)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1425)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows217 : BasisRows generators 217 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator143 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator142 archiveGenerator324))] (
  .cons [archiveGenerator1512] (
  .cons [(.mul archiveGenerator0 archiveGenerator1498),
      (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator92 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator131 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator95 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1348))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1217),
      (.mul archiveGenerator2 (.mul archiveGenerator134 archiveGenerator324))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1216),
      (.mul archiveGenerator3 archiveGenerator1358),
      (.mul archiveGenerator1 (.mul archiveGenerator139 archiveGenerator324))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1216)),
      (.mul archiveGenerator1 archiveGenerator1479),
      (.mul archiveGenerator0 (.mul archiveGenerator141 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1418)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1417))] (
  .cons [archiveGenerator1511,
      (.mul archiveGenerator144 archiveGenerator324),
      (.mul archiveGenerator7 archiveGenerator1215),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1345)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1479)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1478)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator128 archiveGenerator324))))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1213),
      (.mul archiveGenerator3 archiveGenerator1355),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1215)),
      (.mul archiveGenerator1 archiveGenerator1477),
      (.mul archiveGenerator0 archiveGenerator1496),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1178)))] (
  .cons [archiveGenerator1510,
      (.mul archiveGenerator3 archiveGenerator1354),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1332))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1418))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1417)))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1210),
      (.mul archiveGenerator3 archiveGenerator1353),
      (.mul archiveGenerator0 archiveGenerator1495),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator80 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1331))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455)))] (
  .cons [archiveGenerator1509,
      (.mul archiveGenerator2 archiveGenerator1435),
      (.mul archiveGenerator0 archiveGenerator1494),
      (.mul archiveGenerator0 archiveGenerator1493),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator79 archiveGenerator324))))] (
  .cons [archiveGenerator1508,
      (.mul archiveGenerator7 archiveGenerator1208)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1323)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1185))] (
  .cons [archiveGenerator1507,
      (.mul archiveGenerator1 (.mul archiveGenerator137 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1447)))] (
  .cons [archiveGenerator1506,
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator787)),
      (.mul archiveGenerator0 archiveGenerator1491),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1175)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator190))),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator376))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1445))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1154))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator373))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator209 archiveGenerator209))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator189))),
      (.mul archiveGenerator1 archiveGenerator1476),
      (.mul archiveGenerator0 archiveGenerator1489)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator188))),
      (.mul archiveGenerator2 archiveGenerator1430),
      (.mul archiveGenerator0 archiveGenerator1487)] (
  .cons [archiveGenerator1505,
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator618)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator78 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1062),
      (.mul archiveGenerator1 archiveGenerator1474),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator77 archiveGenerator324))))] (
  .cons [archiveGenerator1504,
      (.mul archiveGenerator8 archiveGenerator1170),
      (.mul archiveGenerator1 archiveGenerator1473),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator50 archiveGenerator324)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1169),
      (.mul archiveGenerator0 archiveGenerator1484)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator164))))),
      (.mul archiveGenerator8 (.mul archiveGenerator149 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator1483)] (
  .cons [archiveGenerator1503,
      (.mul archiveGenerator149 archiveGenerator293),
      (.mul archiveGenerator64 archiveGenerator586),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator95)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator140 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1441)))] (
  .cons [archiveGenerator1502] (
  .cons [(.mul archiveGenerator17 archiveGenerator963)] (
  .cons [(.mul archiveGenerator16 archiveGenerator963),
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator784))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator864))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator642)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator890)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator113 archiveGenerator260)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1383))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator889)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator380)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1401)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1167),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator558))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator897))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator149 archiveGenerator206)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator260)))))))] (
  .cons [archiveGenerator1501,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator138))))))] (
  .cons [archiveGenerator1500,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator725))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator452)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator725))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator403))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator725))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator402)))] (
  .cons [] (
  .cons [archiveGenerator1499,
      (.mul archiveGenerator1 archiveGenerator1471)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1471))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator953))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1142)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1468)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1141)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator917)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1395)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1140))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1139))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1467)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows218 : BasisRows generators 218 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator143 archiveGenerator324))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator142 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator143 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator142 archiveGenerator324)))] (
  .cons [archiveGenerator1532,
      (.mul archiveGenerator1 (.mul archiveGenerator7 (.mul archiveGenerator92 archiveGenerator324)))] (
  .cons [archiveGenerator1531,
      (.mul archiveGenerator7 archiveGenerator1237),
      (.mul archiveGenerator3 (.mul archiveGenerator121 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator92 archiveGenerator324))))] (
  .cons [archiveGenerator1530,
      (.mul archiveGenerator7 archiveGenerator1235),
      (.mul archiveGenerator3 (.mul archiveGenerator120 archiveGenerator324)),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1237)),
      (.mul archiveGenerator2 archiveGenerator1464)] (
  .cons [archiveGenerator1529,
      (.mul archiveGenerator3 archiveGenerator1380),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1235)),
      (.mul archiveGenerator2 archiveGenerator1463),
      (.mul archiveGenerator2 archiveGenerator1462),
      (.mul archiveGenerator2 archiveGenerator1461)] (
  .cons [archiveGenerator1528,
      (.mul archiveGenerator7 archiveGenerator1232),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1234)),
      (.mul archiveGenerator2 archiveGenerator1460),
      (.mul archiveGenerator1 (.mul archiveGenerator141 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1216)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1358))] (
  .cons [archiveGenerator1527,
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1230)),
      (.mul archiveGenerator2 archiveGenerator1458),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator1345)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1216))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator141 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1418)))] (
  .cons [archiveGenerator1526,
      archiveGenerator1525,
      (.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator324)),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1227)),
      (.mul archiveGenerator2 archiveGenerator1454),
      (.mul archiveGenerator0 archiveGenerator1511),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1345))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator128 archiveGenerator324)))))))] (
  .cons [archiveGenerator1524,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator33 archiveGenerator324))),
      (.mul archiveGenerator8 (.mul archiveGenerator89 archiveGenerator324)),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1226)),
      (.mul archiveGenerator2 archiveGenerator1453),
      (.mul archiveGenerator2 archiveGenerator1452),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1215))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1496))] (
  .cons [archiveGenerator1523,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator32 archiveGenerator324))),
      (.mul archiveGenerator2 (.mul archiveGenerator43 archiveGenerator719)),
      (.mul archiveGenerator0 archiveGenerator1510)] (
  .cons [(.mul archiveGenerator13 archiveGenerator1091),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1495)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455))))] (
  .cons [(.mul archiveGenerator147 archiveGenerator324),
      (.mul archiveGenerator13 archiveGenerator1089),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator51 archiveGenerator324))),
      (.mul archiveGenerator0 archiveGenerator1509),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1494))] (
  .cons [archiveGenerator1522,
      (.mul archiveGenerator146 archiveGenerator324),
      (.mul archiveGenerator13 archiveGenerator1088),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator324)))),
      (.mul archiveGenerator2 archiveGenerator1446),
      (.mul archiveGenerator0 archiveGenerator1508),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1208))] (
  .cons [archiveGenerator1521,
      (.mul archiveGenerator13 archiveGenerator1087),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator324)))),
      (.mul archiveGenerator2 archiveGenerator1445),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1446)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1185)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator324))))),
      (.mul archiveGenerator1 archiveGenerator1491),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1447))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator88 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator209 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1491)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324))))] (
  .cons [archiveGenerator1520,
      archiveGenerator1519,
      (.mul archiveGenerator188 archiveGenerator250),
      (.mul archiveGenerator16 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1445))))] (
  .cons [(.mul archiveGenerator187 archiveGenerator250),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator50 archiveGenerator324))),
      (.mul archiveGenerator2 archiveGenerator1444),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator209 archiveGenerator209)))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator1124),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator49 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1489))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator629)),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator761)),
      (.mul archiveGenerator1 (.mul archiveGenerator209 archiveGenerator215)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1487))] (
  .cons [archiveGenerator1518,
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator209))),
      (.mul archiveGenerator2 archiveGenerator1442),
      (.mul archiveGenerator0 archiveGenerator1505)] (
  .cons [archiveGenerator1517,
      archiveGenerator1516,
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator628)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator101 archiveGenerator209))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1442))] (
  .cons [(.mul archiveGenerator145 archiveGenerator324),
      (.mul archiveGenerator13 archiveGenerator1079),
      (.mul archiveGenerator9 archiveGenerator1122),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator294)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator692))),
      (.mul archiveGenerator3 archiveGenerator1368),
      (.mul archiveGenerator1 archiveGenerator1484),
      (.mul archiveGenerator0 archiveGenerator1504)] (
  .cons [(.mul archiveGenerator23 archiveGenerator900),
      (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator690)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator261))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1441)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1484))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator760)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator901)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator423)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1483))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator209))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator690))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator261))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator586)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator140 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1441))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator601),
      (.mul archiveGenerator59 archiveGenerator627),
      (.mul archiveGenerator17 archiveGenerator974),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator420)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator294)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator599),
      (.mul archiveGenerator16 archiveGenerator974),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator168))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator346)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator209)))))),
      (.mul archiveGenerator1 archiveGenerator1481),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator963))] (
  .cons [(.mul archiveGenerator64 archiveGenerator598),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator897)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator293))))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator963))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator260))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator316)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator318)))))] (
  .cons [archiveGenerator1515,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator518)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator292)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator248))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator517)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator316)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator380))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator689))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1401))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator278)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator688))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator194)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator558))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator160))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator380)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator219))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator257))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator516)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator218)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator138)))))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator759),
      (.mul archiveGenerator8 archiveGenerator1181),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator167)))))),
      (.mul archiveGenerator0 archiveGenerator1500),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137)))))))] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator623)),
      (.mul archiveGenerator8 archiveGenerator1180),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator149)))))))] (
  .cons [(.mul archiveGenerator113 archiveGenerator452),
      (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator759)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator315)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator595),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator896)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator245)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator244)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator244)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator687))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator403))))] (
  .cons [archiveGenerator1514,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator686)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator452)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator685))),
      (.mul archiveGenerator0 archiveGenerator1499)] (
  .cons [(.mul archiveGenerator8 archiveGenerator1179),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1471)))] (
  .cons [(.mul archiveGenerator49 archiveGenerator686)] (
  .cons [(.mul archiveGenerator17 archiveGenerator969)] (
  .cons [(.mul archiveGenerator16 archiveGenerator969)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1142))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1468))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1141))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator917))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1395))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1480)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1140)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1139)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1513] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows219 : BasisRows generators 219 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator148 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator143 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1512),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator142 archiveGenerator324))))] (
  .cons [] (
  .cons [archiveGenerator1549,
      (.mul archiveGenerator13 (.mul archiveGenerator76 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1531)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1530),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator120 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1464))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1529),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1380))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1479)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1232)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1358)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator144 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1215)),
      (.mul archiveGenerator0 archiveGenerator1527),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator141 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1213)),
      (.mul archiveGenerator0 archiveGenerator1525),
      (.mul archiveGenerator0 (.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1454)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator128 archiveGenerator324))))))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1510),
      (.mul archiveGenerator0 archiveGenerator1524),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator89 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1453))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1387),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1210)),
      (.mul archiveGenerator0 archiveGenerator1523),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1510))] (
  .cons [archiveGenerator1548,
      (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator965)),
      (.mul archiveGenerator1 archiveGenerator1509),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455)))))] (
  .cons [archiveGenerator1547,
      (.mul archiveGenerator0 (.mul archiveGenerator147 archiveGenerator324))] (
  .cons [archiveGenerator1546,
      (.mul archiveGenerator0 archiveGenerator1522),
      (.mul archiveGenerator0 (.mul archiveGenerator146 archiveGenerator324))] (
  .cons [archiveGenerator1545,
      archiveGenerator1544,
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator137 archiveGenerator324))),
      (.mul archiveGenerator0 archiveGenerator1521),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1445))] (
  .cons [archiveGenerator1543,
      (.mul archiveGenerator68 archiveGenerator604),
      (.mul archiveGenerator13 archiveGenerator1096),
      (.mul archiveGenerator1 archiveGenerator1506),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1447)))))] (
  .cons [archiveGenerator1542,
      archiveGenerator1541,
      (.mul archiveGenerator67 archiveGenerator604),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324)))))] (
  .cons [archiveGenerator1540,
      (.mul archiveGenerator0 archiveGenerator1519),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1445)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator532))),
      (.mul archiveGenerator9 archiveGenerator1148),
      (.mul archiveGenerator3 archiveGenerator1386),
      (.mul archiveGenerator0 (.mul archiveGenerator187 archiveGenerator250)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator50 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator209 archiveGenerator209))))))] (
  .cons [archiveGenerator1539,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator288)))),
      (.mul archiveGenerator8 archiveGenerator1205),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator49 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator187 archiveGenerator255)] (
  .cons [(.mul archiveGenerator64 archiveGenerator610),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator188)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator287)))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator212))),
      (.mul archiveGenerator0 archiveGenerator1517),
      (.mul archiveGenerator0 archiveGenerator1516)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator286)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator640))),
      (.mul archiveGenerator0 (.mul archiveGenerator145 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1504))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator705)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator704))),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator586)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1483)))] (
  .cons [archiveGenerator1538,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator188)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator586))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1441)))))] (
  .cons [archiveGenerator1537,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator187)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator267))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator601)),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator974))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator920)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator188)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator974)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator963)))] (
  .cons [archiveGenerator1536,
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator434)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator212)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator598)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator897)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator299)),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator530)))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator64))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator255))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))))))] (
  .cons [archiveGenerator1535,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator327))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator72)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator101)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator404)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator80)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator558)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator529)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator101))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator185)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator64))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator138))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator184)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator154))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator137))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator778)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator51))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator623)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator918)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator23)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator759)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator433)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator29)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator896)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator432)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator138)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator9))))))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator452)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator225)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator100))))))))] (
  .cons [archiveGenerator1534,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator224)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator40)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator402))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator56))))))))),
      (.mul archiveGenerator0 archiveGenerator1514)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator403)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator55))))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1471))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator403)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator223)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1499))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator402)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator117))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1471))))] (
  .cons [(.mul archiveGenerator59 archiveGenerator635),
      (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator636)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator153)))))))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator636)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator152))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator969))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator917)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator528)))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator969))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator916)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator253)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator326)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator325))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator915)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator579)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator701)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator700)))] (
  .cons [archiveGenerator1533] (
  .cons [(.mul archiveGenerator17 archiveGenerator996)] (
  .cons [(.mul archiveGenerator8 archiveGenerator1203)] (
  .cons [(.mul archiveGenerator8 archiveGenerator1202)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows220 : BasisRows generators 220 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator143 archiveGenerator324)))] (
  .cons [archiveGenerator1565,
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator142 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1286),
      (.mul archiveGenerator2 archiveGenerator1498),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator143 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1284),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1424)),
      (.mul archiveGenerator1 archiveGenerator1532),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator142 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator1282),
      (.mul archiveGenerator7 archiveGenerator1281),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1422)),
      (.mul archiveGenerator1 archiveGenerator1531)] (
  .cons [(.mul archiveGenerator7 archiveGenerator1280),
      (.mul archiveGenerator1 archiveGenerator1530),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1235)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1531))] (
  .cons [(.mul archiveGenerator3 archiveGenerator1415),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1418)),
      (.mul archiveGenerator1 archiveGenerator1529),
      (.mul archiveGenerator0 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1530))] (
  .cons [archiveGenerator1564,
      (.mul archiveGenerator151 archiveGenerator324),
      (.mul archiveGenerator7 archiveGenerator1274),
      (.mul archiveGenerator7 archiveGenerator1273),
      (.mul archiveGenerator1 archiveGenerator1528),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1529)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1380)))] (
  .cons [archiveGenerator1563,
      (.mul archiveGenerator150 archiveGenerator324),
      (.mul archiveGenerator7 archiveGenerator1271),
      (.mul archiveGenerator3 archiveGenerator1411),
      (.mul archiveGenerator2 archiveGenerator1496),
      (.mul archiveGenerator1 archiveGenerator1527),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1232)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1120),
      (.mul archiveGenerator7 archiveGenerator1270),
      (.mul archiveGenerator3 archiveGenerator1410),
      (.mul archiveGenerator1 archiveGenerator1526),
      (.mul archiveGenerator1 archiveGenerator1525),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1527))] (
  .cons [archiveGenerator1562,
      (.mul archiveGenerator13 archiveGenerator1118),
      (.mul archiveGenerator7 archiveGenerator1269),
      (.mul archiveGenerator7 archiveGenerator1268),
      (.mul archiveGenerator2 archiveGenerator1495),
      (.mul archiveGenerator1 archiveGenerator1524),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1525)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 (.mul archiveGenerator80 archiveGenerator324))))] (
  .cons [archiveGenerator1561,
      (.mul archiveGenerator149 archiveGenerator324),
      (.mul archiveGenerator7 archiveGenerator1267),
      (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator988)),
      (.mul archiveGenerator1 archiveGenerator1523),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1524))] (
  .cons [archiveGenerator1560,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1387)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1523))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1548),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455))))))] (
  .cons [archiveGenerator1559,
      (.mul archiveGenerator1 archiveGenerator1522),
      (.mul archiveGenerator0 archiveGenerator1547),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator147 archiveGenerator324)))] (
  .cons [archiveGenerator1558,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator787)),
      (.mul archiveGenerator1 archiveGenerator1521),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator146 archiveGenerator324)))] (
  .cons [] (
  .cons [archiveGenerator1557,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1447))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator569))),
      (.mul archiveGenerator1 archiveGenerator1519),
      (.mul archiveGenerator0 archiveGenerator1541),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator604)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324))))))] (
  .cons [archiveGenerator1556,
      archiveGenerator1555,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1519)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1445))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator212))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1386)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator50 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator417))),
      (.mul archiveGenerator0 archiveGenerator1539),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator49 archiveGenerator324)))))] (
  .cons [archiveGenerator1554,
      (.mul archiveGenerator9 archiveGenerator1170),
      (.mul archiveGenerator3 archiveGenerator1404)] (
  .cons [(.mul archiveGenerator8 archiveGenerator1221),
      (.mul archiveGenerator2 archiveGenerator1484)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator160 archiveGenerator209)),
      (.mul archiveGenerator1 (.mul archiveGenerator145 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1484))] (
  .cons [(.mul archiveGenerator160 archiveGenerator293),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator145 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1504)))] (
  .cons [archiveGenerator1553,
      (.mul archiveGenerator149 archiveGenerator318),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator75))))))] (
  .cons [(.mul archiveGenerator20 archiveGenerator963),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator537))),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator105)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1483))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator784)),
      (.mul archiveGenerator8 archiveGenerator1220),
      (.mul archiveGenerator1 (.mul archiveGenerator59 archiveGenerator627)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator586)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1441))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator864)),
      (.mul archiveGenerator0 archiveGenerator1537),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator601))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator974)))] (
  .cons [archiveGenerator1552,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator642))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator963))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator715))),
      (.mul archiveGenerator1 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149))),
      (.mul archiveGenerator0 archiveGenerator1536),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator598))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator897))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator928)),
      (.mul archiveGenerator1 archiveGenerator1515),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator260)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator927))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator149 archiveGenerator149)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1219),
      (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator491))] (
  .cons [archiveGenerator1551] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator759))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator896))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1534)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1514))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1499)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1471)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator636)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator636))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator969)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator917))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator969)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator916)))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator996))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1203))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1202))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1550] (
  .cons [(.mul archiveGenerator1 archiveGenerator1513)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows221 : BasisRows generators 221 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator148 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1565)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1286)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1498)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator143 archiveGenerator324))))))] (
  .cons [archiveGenerator1584,
      (.mul archiveGenerator2 (.mul archiveGenerator7 (.mul archiveGenerator95 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1284))] (
  .cons [archiveGenerator1583,
      (.mul archiveGenerator1 archiveGenerator1549),
      (.mul archiveGenerator1 (.mul archiveGenerator13 (.mul archiveGenerator76 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1281))] (
  .cons [archiveGenerator1582,
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1280)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1531)))] (
  .cons [(.mul archiveGenerator155 archiveGenerator324),
      (.mul archiveGenerator4 archiveGenerator1380)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1564),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1273))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator101 archiveGenerator324)),
      (.mul archiveGenerator7 archiveGenerator1297),
      (.mul archiveGenerator7 archiveGenerator1296),
      (.mul archiveGenerator3 archiveGenerator1436)] (
  .cons [archiveGenerator1581,
      (.mul archiveGenerator7 archiveGenerator1295),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1270)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1527)))] (
  .cons [(.mul archiveGenerator154 archiveGenerator324),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator324)))),
      (.mul archiveGenerator3 archiveGenerator1435),
      (.mul archiveGenerator0 archiveGenerator1562)] (
  .cons [archiveGenerator1580,
      (.mul archiveGenerator17 (.mul archiveGenerator64 archiveGenerator324)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator51 archiveGenerator324))),
      (.mul archiveGenerator2 archiveGenerator1509),
      (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1267))] (
  .cons [archiveGenerator1579,
      archiveGenerator1578,
      archiveGenerator1577,
      (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator324)),
      (.mul archiveGenerator9 (.mul archiveGenerator75 archiveGenerator373)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator324)))),
      (.mul archiveGenerator1 archiveGenerator1548),
      (.mul archiveGenerator0 archiveGenerator1560),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1523)))] (
  .cons [archiveGenerator1576,
      (.mul archiveGenerator13 (.mul archiveGenerator67 archiveGenerator373)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator29 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1548)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator324))))),
      (.mul archiveGenerator0 archiveGenerator1559)] (
  .cons [archiveGenerator1575,
      (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator335)),
      (.mul archiveGenerator8 (.mul archiveGenerator100 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator146 archiveGenerator324))))] (
  .cons [archiveGenerator1574,
      (.mul archiveGenerator188 archiveGenerator261),
      (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator40 archiveGenerator324))),
      (.mul archiveGenerator1 archiveGenerator1543)] (
  .cons [archiveGenerator1573,
      (.mul archiveGenerator187 archiveGenerator261),
      (.mul archiveGenerator13 archiveGenerator1125),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator56 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324)))))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1124),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator55 archiveGenerator324))),
      (.mul archiveGenerator3 archiveGenerator1430),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324)))))))] (
  .cons [archiveGenerator1572,
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1430)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1519)))] (
  .cons [archiveGenerator1571,
      archiveGenerator1570,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator209))),
      (.mul archiveGenerator2 archiveGenerator1505),
      (.mul archiveGenerator1 archiveGenerator1539)] (
  .cons [archiveGenerator1569,
      (.mul archiveGenerator153 archiveGenerator324),
      (.mul archiveGenerator13 archiveGenerator1123),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator181))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator101 archiveGenerator209))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1539))] (
  .cons [(.mul archiveGenerator188 archiveGenerator260),
      (.mul archiveGenerator152 archiveGenerator324),
      (.mul archiveGenerator13 archiveGenerator1122),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator294)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator692))),
      (.mul archiveGenerator0 archiveGenerator1554)] (
  .cons [(.mul archiveGenerator64 archiveGenerator627),
      (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator690)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator729))),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator1484))] (
  .cons [archiveGenerator1568,
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator901)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator280))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator423))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator279))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator690))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator261)))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator1035),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator420)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator294))))),
      (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator318))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator113 archiveGenerator292)),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator455)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator346)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator209)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1483)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator624),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator940)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator350))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator586))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1441)))))))] (
  .cons [(.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator160)),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator278))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator346)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator348))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator601)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator974))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator550)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator292))))),
      (.mul archiveGenerator0 archiveGenerator1552),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator963)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator248))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator347))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator346))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1536)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator598))))] (
  .cons [(.mul archiveGenerator113 archiveGenerator491),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator260)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator549)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator623),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator292)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator726))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator194)))))),
      (.mul archiveGenerator1 archiveGenerator1535)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator598))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator260))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator219))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator149)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator260))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator233))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator60 archiveGenerator491)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator939)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator232))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator137 archiveGenerator245)),
      (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator491))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator160)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator138 archiveGenerator244)),
      (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator491))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator345)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator452)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator725))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator344)))))] (
  .cons [archiveGenerator1567,
      archiveGenerator1566,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator257)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator343)))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator1033),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator724)))] (
  .cons [(.mul archiveGenerator16 archiveGenerator1033),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator723)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator595)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator722)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1241),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1514)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1240)] (
  .cons [(.mul archiveGenerator17 archiveGenerator1030),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1499))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1239),
      (.mul archiveGenerator1 (.mul archiveGenerator59 archiveGenerator635)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1471))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator636))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator969))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator917))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator916))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397)))))))))] (
  .cons [(.mul archiveGenerator5 archiveGenerator1312),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396)))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1203)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator1202)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1550)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows222 : BasisRows generators 222 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator158 archiveGenerator324)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1565))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1286)))] (
  .cons [(.mul archiveGenerator157 archiveGenerator324),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1281)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1284)))] (
  .cons [archiveGenerator1603,
      (.mul archiveGenerator9 (.mul archiveGenerator95 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator1583),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1281)))] (
  .cons [archiveGenerator1602,
      (.mul archiveGenerator13 (.mul archiveGenerator83 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1531))))] (
  .cons [archiveGenerator1601,
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1273)),
      (.mul archiveGenerator0 (.mul archiveGenerator155 archiveGenerator324))] (
  .cons [(.mul archiveGenerator156 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1564)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1273)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1525)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator101 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1297)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1296))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1268)),
      (.mul archiveGenerator0 archiveGenerator1581),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1295)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1270))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1527))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1561),
      (.mul archiveGenerator1 (.mul archiveGenerator149 archiveGenerator324)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator988))),
      (.mul archiveGenerator0 (.mul archiveGenerator154 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1562))] (
  .cons [archiveGenerator1600,
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator64 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1267)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1577),
      (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1523))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1156),
      (.mul archiveGenerator0 archiveGenerator1576),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455))))))))] (
  .cons [archiveGenerator1599,
      (.mul archiveGenerator67 archiveGenerator630),
      (.mul archiveGenerator13 archiveGenerator1154),
      (.mul archiveGenerator1 archiveGenerator1558)] (
  .cons [(.mul archiveGenerator67 archiveGenerator629),
      (.mul archiveGenerator13 archiveGenerator1153),
      (.mul archiveGenerator0 archiveGenerator1575)] (
  .cons [(.mul archiveGenerator25 archiveGenerator959),
      (.mul archiveGenerator13 archiveGenerator1150),
      (.mul archiveGenerator3 archiveGenerator1444),
      (.mul archiveGenerator1 archiveGenerator1557)] (
  .cons [(.mul archiveGenerator24 archiveGenerator959),
      (.mul archiveGenerator13 archiveGenerator1148),
      (.mul archiveGenerator3 archiveGenerator1443),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1519)),
      (.mul archiveGenerator0 archiveGenerator1573),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324))))))))] (
  .cons [archiveGenerator1598,
      (.mul archiveGenerator23 archiveGenerator959),
      (.mul archiveGenerator8 (.mul archiveGenerator188 archiveGenerator188)),
      (.mul archiveGenerator1 archiveGenerator1556),
      (.mul archiveGenerator1 archiveGenerator1555),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324))))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator331)))),
      (.mul archiveGenerator8 (.mul archiveGenerator187 archiveGenerator188)),
      (.mul archiveGenerator3 archiveGenerator1442),
      (.mul archiveGenerator0 archiveGenerator1572)] (
  .cons [archiveGenerator1597,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator190))))),
      (.mul archiveGenerator8 (.mul archiveGenerator187 archiveGenerator187)),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator1442)),
      (.mul archiveGenerator0 archiveGenerator1571)] (
  .cons [archiveGenerator1596,
      (.mul archiveGenerator64 archiveGenerator638),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator212))),
      (.mul archiveGenerator1 archiveGenerator1554),
      (.mul archiveGenerator0 (.mul archiveGenerator153 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1539)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator189))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator640))),
      (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator260)),
      (.mul archiveGenerator0 (.mul archiveGenerator152 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1554))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188))))),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator328)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator705))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator145 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator627))] (
  .cons [archiveGenerator1595,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator303)))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator738)))] (
  .cons [archiveGenerator1594,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator188))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator72 archiveGenerator188))))] (
  .cons [archiveGenerator1593,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator201)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator267)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator957)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator113 archiveGenerator292))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1483))))))] (
  .cons [archiveGenerator1592,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator52))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator956)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator212)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator940))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator586))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator113))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator267))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator278)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator601))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator974)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator112))),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator188)))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator963))))))] (
  .cons [(.mul archiveGenerator138 archiveGenerator404),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator188)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1536))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator598)))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator637),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator187)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator101))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator113 archiveGenerator491)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator559)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator80)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator623))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator557)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator101)))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator491)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator138))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator113))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator137))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator162))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator955)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator113)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator51))))))))),
      (.mul archiveGenerator5 (.mul archiveGenerator149 archiveGenerator244))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator954)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator112)))))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator23)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator225))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator147)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator32)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator725))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator224))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator185)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator13))))))))))),
      (.mul archiveGenerator0 archiveGenerator1566)] (
  .cons [archiveGenerator1591,
      archiveGenerator1590,
      archiveGenerator1589,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator238)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator60)))))))))] (
  .cons [(.mul archiveGenerator138 archiveGenerator403),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator237)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator17)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator1033))] (
  .cons [(.mul archiveGenerator64 archiveGenerator636),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator298)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17)))))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator1033))] (
  .cons [(.mul archiveGenerator64 archiveGenerator635),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator433)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator556)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator161)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator555)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator50))))))))] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator663)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator111))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator806)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator110)))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1499)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator953)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator354))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1471)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator952)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator183)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator636)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator183)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator969)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator236))))))] (
  .cons [archiveGenerator1588,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator736)))] (
  .cons [archiveGenerator1587,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator296))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator554)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator553)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396))))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1254)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator804))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator804))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator951))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator1586] (
  .cons [archiveGenerator1585] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1550))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows223 : BasisRows generators 223 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator1584)] (
  .cons [(.mul archiveGenerator1 archiveGenerator1583)] (
  .cons [(.mul archiveGenerator1 archiveGenerator1582),
      (.mul archiveGenerator0 archiveGenerator1603),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1281))))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1332)),
      (.mul archiveGenerator1 (.mul archiveGenerator4 archiveGenerator1380)),
      (.mul archiveGenerator0 archiveGenerator1602),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1531)))))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator1330)),
      (.mul archiveGenerator0 archiveGenerator1601)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator1297)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator13 (.mul archiveGenerator80 archiveGenerator324))))] (
  .cons [archiveGenerator1617,
      (.mul archiveGenerator160 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1296)))] (
  .cons [archiveGenerator1616,
      archiveGenerator1615,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1295)))] (
  .cons [archiveGenerator1614,
      archiveGenerator1613,
      (.mul archiveGenerator2 archiveGenerator1548),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator154 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1562)))] (
  .cons [archiveGenerator1612,
      (.mul archiveGenerator1 archiveGenerator1577),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1548)),
      (.mul archiveGenerator0 archiveGenerator1600),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator64 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator149 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator1267))))] (
  .cons [archiveGenerator1611,
      archiveGenerator1610,
      archiveGenerator1609,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator324)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1523)))))] (
  .cons [(.mul archiveGenerator209 archiveGenerator250),
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator867)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1455)))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator213))),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator570))),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator630))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator569))),
      (.mul archiveGenerator1 archiveGenerator1574),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator629))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator76 archiveGenerator212))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1444))] (
  .cons [archiveGenerator1608,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator75 archiveGenerator212))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1573)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator324)))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator822)),
      (.mul archiveGenerator2 archiveGenerator1539),
      (.mul archiveGenerator1 archiveGenerator1572),
      (.mul archiveGenerator0 archiveGenerator1598),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator137 archiveGenerator324)))))))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator1170),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator1539)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator1442)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1572))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator167 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator1597),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1571))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator166 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator1596),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator153 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1539))))] (
  .cons [archiveGenerator1607,
      (.mul archiveGenerator64 archiveGenerator645),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator76)))))),
      (.mul archiveGenerator8 archiveGenerator1290),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator627)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator188 archiveGenerator260))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator152 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator159 archiveGenerator324),
      (.mul archiveGenerator149 archiveGenerator348),
      (.mul archiveGenerator23 archiveGenerator963),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator75)))))),
      (.mul archiveGenerator1 archiveGenerator1568),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator627)))] (
  .cons [archiveGenerator1606,
      (.mul archiveGenerator22 archiveGenerator963)] (
  .cons [(.mul archiveGenerator64 archiveGenerator642),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator963))] (
  .cons [(.mul archiveGenerator193 archiveGenerator260),
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator864))] (
  .cons [archiveGenerator1605,
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator642)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator715))),
      (.mul archiveGenerator0 archiveGenerator1592),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator940)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator586)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator753))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator601)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator974))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator962))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator149 archiveGenerator160))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator598))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1288),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator637)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator113 archiveGenerator491))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 (.mul archiveGenerator64 archiveGenerator149)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator1287),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator623)))] (
  .cons [archiveGenerator1604] (
  .cons [(.mul archiveGenerator149 archiveGenerator343)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator491)))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator1566),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator725)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1566))] (
  .cons [(.mul archiveGenerator0 archiveGenerator1591),
      (.mul archiveGenerator0 archiveGenerator1589)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator138 archiveGenerator403)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator1033)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator636)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator1033)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator635))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator806))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1499))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator953))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1471))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator952))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator636))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator969))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1588)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1587)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator1312)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1397)))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator1396)))))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator804)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator951)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator1586)] (
  .cons [(.mul archiveGenerator0 archiveGenerator1585)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end KIP126.Computation.StandardArchive
