module

import all KIP126.AdamsComputation.Internal.SphereArchive.Basic
import all KIP126.AdamsComputation.Internal.SphereArchive.Generators

/-! Ordered S⁰ basis monomials in internal degrees 128–159.
Standard supplies their Adams E₂ interpretation. -/

@[expose] section
namespace KIP126.Computation.StandardArchive
open KIP126.Computation
set_option backward.privateInPublic true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private noncomputable def archiveMonomialRows128 : BasisRows generators 128 0 :=
  .cons [] (
  .cons [archiveGenerator324] (
  .cons [(.mul archiveGenerator69 archiveGenerator69)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator323,
      (.mul archiveGenerator68 archiveGenerator69)] (
  .cons [(.mul archiveGenerator67 archiveGenerator69)] (
  .cons [archiveGenerator322] (
  .cons [archiveGenerator321,
      (.mul archiveGenerator3 archiveGenerator270),
      (.mul archiveGenerator0 archiveGenerator314)] (
  .cons [archiveGenerator320,
      (.mul archiveGenerator0 archiveGenerator312),
      (.mul archiveGenerator0 archiveGenerator311)] (
  .cons [(.mul archiveGenerator68 archiveGenerator68),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator69))] (
  .cons [archiveGenerator319,
      (.mul archiveGenerator67 archiveGenerator68)] (
  .cons [(.mul archiveGenerator67 archiveGenerator67),
      (.mul archiveGenerator9 archiveGenerator209),
      (.mul archiveGenerator1 archiveGenerator308)] (
  .cons [(.mul archiveGenerator3 archiveGenerator267),
      (.mul archiveGenerator1 (.mul archiveGenerator13 archiveGenerator189))] (
  .cons [archiveGenerator318,
      (.mul archiveGenerator3 archiveGenerator266),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator286)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator306))] (
  .cons [(.mul archiveGenerator1 archiveGenerator302),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator304)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator188)))] (
  .cons [archiveGenerator317,
      archiveGenerator316,
      (.mul archiveGenerator1 archiveGenerator300),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator59 archiveGenerator69)))))] (
  .cons [(.mul archiveGenerator23 archiveGenerator150),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator301)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300))] (
  .cons [(.mul archiveGenerator13 archiveGenerator194),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator292)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator219),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator64)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator299))] (
  .cons [(.mul archiveGenerator8 archiveGenerator218),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator64)))] (
  .cons [(.mul archiveGenerator16 archiveGenerator167)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator149))] (
  .cons [archiveGenerator315] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator147))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator154))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator298))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator297))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator111))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator145))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator295),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator296))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator295))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows129 : BasisRows generators 129 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator324)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator69))] (
  .cons [archiveGenerator333] (
  .cons [archiveGenerator332,
      (.mul archiveGenerator0 archiveGenerator322)] (
  .cons [archiveGenerator331,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator270)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator314))] (
  .cons [archiveGenerator330,
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator312)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator311))] (
  .cons [archiveGenerator329,
      (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator68)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator319),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator68))] (
  .cons [archiveGenerator328,
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator67))] (
  .cons [(.mul archiveGenerator9 archiveGenerator212),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator267))] (
  .cons [(.mul archiveGenerator0 archiveGenerator318),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator266))] (
  .cons [(.mul archiveGenerator2 archiveGenerator292)] (
  .cons [archiveGenerator327,
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80)),
      (.mul archiveGenerator0 archiveGenerator317),
      (.mul archiveGenerator0 archiveGenerator316)] (
  .cons [(.mul archiveGenerator64 archiveGenerator72),
      (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator101)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator301))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator80))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator292))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator101))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator299)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator64)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator64))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator154)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator51))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator23)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator29)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator9))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator225),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator100)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator224),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator40))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator56))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator55))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator223),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator297)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator117)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator153)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245)))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator152))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator326] (
  .cons [archiveGenerator325] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator296)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows130 : BasisRows generators 130 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator324)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))] (
  .cons [archiveGenerator341,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [archiveGenerator340] (
  .cons [archiveGenerator339] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator323)] (
  .cons [archiveGenerator338,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator69)))] (
  .cons [archiveGenerator337,
      (.mul archiveGenerator1 archiveGenerator322),
      (.mul archiveGenerator0 archiveGenerator333)] (
  .cons [archiveGenerator336,
      (.mul archiveGenerator69 archiveGenerator72),
      (.mul archiveGenerator1 archiveGenerator321),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator270))] (
  .cons [archiveGenerator335,
      (.mul archiveGenerator1 archiveGenerator320),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator314)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator312))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator311)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator319)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator308)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator319))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator13 archiveGenerator188)),
      (.mul archiveGenerator0 archiveGenerator328)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator133)),
      (.mul archiveGenerator2 archiveGenerator302),
      (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator267)))] (
  .cons [archiveGenerator334,
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator83)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator266)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator300)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator292))] (
  .cons [(.mul archiveGenerator0 archiveGenerator327),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator316))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator72)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator301)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator64))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator292)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator299))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator64)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator315),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64))))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator244)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator225))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator224))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator326)] (
  .cons [(.mul archiveGenerator0 archiveGenerator325)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator295))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator296))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows131 : BasisRows generators 131 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator69 archiveGenerator76),
      (.mul archiveGenerator0 archiveGenerator340)] (
  .cons [archiveGenerator353,
      (.mul archiveGenerator69 archiveGenerator75),
      (.mul archiveGenerator0 archiveGenerator339)] (
  .cons [archiveGenerator352] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator338)] (
  .cons [archiveGenerator351,
      (.mul archiveGenerator0 archiveGenerator337),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator333))] (
  .cons [(.mul archiveGenerator67 archiveGenerator76),
      (.mul archiveGenerator0 archiveGenerator336),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator72))] (
  .cons [(.mul archiveGenerator67 archiveGenerator75),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator69))),
      (.mul archiveGenerator0 archiveGenerator335),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator314))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator209),
      (.mul archiveGenerator3 archiveGenerator287),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator312)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator311))))] (
  .cons [archiveGenerator350,
      archiveGenerator349,
      (.mul archiveGenerator3 archiveGenerator285),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator287))] (
  .cons [archiveGenerator348,
      (.mul archiveGenerator1 archiveGenerator328)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator13 archiveGenerator188)))] (
  .cons [archiveGenerator347,
      archiveGenerator346] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator9 archiveGenerator219),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator327)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator233),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator301))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator232)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator160)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator299)))))] (
  .cons [archiveGenerator345,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator64))))))] (
  .cons [archiveGenerator344] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64)))))] (
  .cons [archiveGenerator343] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator225)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator224)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator245)))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator326))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator325))] (
  .cons [archiveGenerator342] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator296)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows132 : BasisRows generators 132 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 archiveGenerator324)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator324))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))] (
  .cons [archiveGenerator368,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator340))] (
  .cons [archiveGenerator367] (
  .cons [archiveGenerator366,
      (.mul archiveGenerator0 archiveGenerator352)] (
  .cons [] (
  .cons [archiveGenerator365] (
  .cons [archiveGenerator364,
      archiveGenerator363,
      (.mul archiveGenerator0 archiveGenerator351),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator337)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator333)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator213),
      (.mul archiveGenerator7 archiveGenerator250),
      (.mul archiveGenerator1 archiveGenerator335),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator336)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator72)))] (
  .cons [archiveGenerator362,
      archiveGenerator361,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator335)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator314)))))] (
  .cons [archiveGenerator360,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator312))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator311)))))] (
  .cons [archiveGenerator359,
      (.mul archiveGenerator13 archiveGenerator212),
      (.mul archiveGenerator0 archiveGenerator349),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator285))] (
  .cons [archiveGenerator358,
      archiveGenerator357] (
  .cons [archiveGenerator356,
      archiveGenerator355,
      (.mul archiveGenerator17 archiveGenerator188)] (
  .cons [(.mul archiveGenerator16 archiveGenerator188),
      (.mul archiveGenerator1 archiveGenerator334),
      (.mul archiveGenerator0 archiveGenerator347),
      (.mul archiveGenerator0 archiveGenerator346)] (
  .cons [(.mul archiveGenerator16 archiveGenerator187),
      (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator101))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator24)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator80)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator101))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator113)),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator301)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator162)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator113))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator51)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator299))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator112))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator64)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator32))))),
      (.mul archiveGenerator0 archiveGenerator344)] (
  .cons [(.mul archiveGenerator17 archiveGenerator185),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator13))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator238),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator60)))),
      (.mul archiveGenerator0 archiveGenerator343)] (
  .cons [(.mul archiveGenerator8 archiveGenerator237),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator17))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator244))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator161))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator50)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator110)))] (
  .cons [archiveGenerator354,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator183)] (
  .cons [(.mul archiveGenerator16 archiveGenerator183)] (
  .cons [(.mul archiveGenerator8 archiveGenerator236)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator325)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows133 : BasisRows generators 133 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [archiveGenerator378] (
  .cons [archiveGenerator377,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator69 archiveGenerator76)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))))))] (
  .cons [archiveGenerator376,
      archiveGenerator375] (
  .cons [archiveGenerator374,
      archiveGenerator373,
      (.mul archiveGenerator0 archiveGenerator367)] (
  .cons [archiveGenerator372,
      (.mul archiveGenerator69 archiveGenerator80),
      (.mul archiveGenerator0 archiveGenerator366)] (
  .cons [archiveGenerator371,
      (.mul archiveGenerator69 archiveGenerator79)] (
  .cons [(.mul archiveGenerator1 archiveGenerator351),
      (.mul archiveGenerator0 archiveGenerator365)] (
  .cons [(.mul archiveGenerator0 archiveGenerator363)] (
  .cons [archiveGenerator370,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator72))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator287)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator314))))))] (
  .cons [archiveGenerator369,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator134)),
      (.mul archiveGenerator2 archiveGenerator328),
      (.mul archiveGenerator1 archiveGenerator349),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator312))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator133)),
      (.mul archiveGenerator0 archiveGenerator359),
      (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator349))] (
  .cons [(.mul archiveGenerator0 archiveGenerator358)] (
  .cons [(.mul archiveGenerator1 archiveGenerator347),
      (.mul archiveGenerator0 archiveGenerator356),
      (.mul archiveGenerator0 archiveGenerator355),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator188))] (
  .cons [(.mul archiveGenerator69 archiveGenerator78),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator347)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator346))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator187))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator260),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300)))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator299)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator64))))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator185))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator238)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator343))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator237))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator183))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator183))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator236))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator342)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows134 : BasisRows generators 134 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator324)))] (
  .cons [archiveGenerator400,
      (.mul archiveGenerator2 archiveGenerator341),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator69))))] (
  .cons [archiveGenerator399,
      archiveGenerator398,
      (.mul archiveGenerator2 archiveGenerator340),
      (.mul archiveGenerator0 archiveGenerator378)] (
  .cons [archiveGenerator397,
      archiveGenerator396,
      (.mul archiveGenerator1 archiveGenerator368),
      (.mul archiveGenerator0 archiveGenerator377),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))] (
  .cons [archiveGenerator395,
      archiveGenerator394,
      archiveGenerator393,
      archiveGenerator392,
      (.mul archiveGenerator69 archiveGenerator85),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69)))))))] (
  .cons [archiveGenerator391,
      archiveGenerator390,
      (.mul archiveGenerator69 archiveGenerator82),
      (.mul archiveGenerator18 archiveGenerator190),
      (.mul archiveGenerator0 archiveGenerator375)] (
  .cons [archiveGenerator389,
      archiveGenerator388,
      (.mul archiveGenerator1 archiveGenerator366),
      (.mul archiveGenerator0 archiveGenerator373),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator367))] (
  .cons [archiveGenerator387,
      archiveGenerator386,
      (.mul archiveGenerator18 archiveGenerator189),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator80)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator366))] (
  .cons [(.mul archiveGenerator18 archiveGenerator188),
      (.mul archiveGenerator0 archiveGenerator371),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator79))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator365))] (
  .cons [archiveGenerator385,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator363))] (
  .cons [archiveGenerator384,
      (.mul archiveGenerator1 archiveGenerator361),
      (.mul archiveGenerator0 archiveGenerator370)] (
  .cons [(.mul archiveGenerator8 archiveGenerator250),
      (.mul archiveGenerator1 archiveGenerator360)] (
  .cons [archiveGenerator383,
      (.mul archiveGenerator1 archiveGenerator359),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator328)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator312)))))))] (
  .cons [archiveGenerator382,
      (.mul archiveGenerator1 archiveGenerator357),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator359)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator349)))] (
  .cons [archiveGenerator381,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator358))] (
  .cons [(.mul archiveGenerator13 archiveGenerator220),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator355)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator188)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator219),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator347)))] (
  .cons [archiveGenerator380,
      (.mul archiveGenerator8 archiveGenerator248)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator167))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator166)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator247),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator245)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator299))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator244)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator238))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator343)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator237)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator354)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator183)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator183)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator236)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator379] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows135 : BasisRows generators 135 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator76)),
      (.mul archiveGenerator0 archiveGenerator398),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator378))] (
  .cons [archiveGenerator415,
      (.mul archiveGenerator2 archiveGenerator353),
      (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator75)),
      (.mul archiveGenerator0 archiveGenerator397),
      (.mul archiveGenerator0 archiveGenerator396),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator377)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))] (
  .cons [archiveGenerator414,
      (.mul archiveGenerator1 archiveGenerator376),
      (.mul archiveGenerator1 archiveGenerator375),
      (.mul archiveGenerator0 archiveGenerator394),
      (.mul archiveGenerator0 archiveGenerator392),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))))))))] (
  .cons [archiveGenerator413,
      archiveGenerator412,
      (.mul archiveGenerator0 archiveGenerator391),
      (.mul archiveGenerator0 archiveGenerator390),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator375))] (
  .cons [archiveGenerator411,
      archiveGenerator410,
      archiveGenerator409,
      (.mul archiveGenerator0 archiveGenerator389),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator367)))] (
  .cons [archiveGenerator408,
      (.mul archiveGenerator0 archiveGenerator386),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator80)))] (
  .cons [archiveGenerator407,
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator351)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator79)))] (
  .cons [archiveGenerator406] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator369)] (
  .cons [archiveGenerator405,
      (.mul archiveGenerator20 archiveGenerator188)] (
  .cons [(.mul archiveGenerator8 archiveGenerator255),
      (.mul archiveGenerator2 archiveGenerator346),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator359))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator349))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101)),
      (.mul archiveGenerator8 archiveGenerator254),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator347)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator358)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator188))))] (
  .cons [archiveGenerator404,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator101))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator347))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator173)),
      (.mul archiveGenerator0 archiveGenerator380)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator80))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator260))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator51)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator118))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300)))))))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator137),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator32)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator138)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator13))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator138)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator63)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator244))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator137)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator20)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator40)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator39)))))] (
  .cons [archiveGenerator403,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator171))] (
  .cons [archiveGenerator402,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator78)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator117)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator116)))] (
  .cons [archiveGenerator401] (
  .cons [(.mul archiveGenerator17 archiveGenerator200)] (
  .cons [(.mul archiveGenerator8 archiveGenerator253)] (
  .cons [(.mul archiveGenerator8 archiveGenerator252),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator183))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows136 : BasisRows generators 136 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator3 archiveGenerator324)] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator324))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [] (
  .cons [(.mul archiveGenerator69 archiveGenerator93)] (
  .cons [(.mul archiveGenerator2 archiveGenerator368)] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator69))] (
  .cons [(.mul archiveGenerator1 archiveGenerator393),
      (.mul archiveGenerator1 archiveGenerator392),
      (.mul archiveGenerator0 archiveGenerator415),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator396)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))] (
  .cons [archiveGenerator419,
      (.mul archiveGenerator0 archiveGenerator414),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator394)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator392)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69)))))))))] (
  .cons [(.mul archiveGenerator69 archiveGenerator89),
      (.mul archiveGenerator1 archiveGenerator389),
      (.mul archiveGenerator1 archiveGenerator388),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator391)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator375)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator387),
      (.mul archiveGenerator0 archiveGenerator410),
      (.mul archiveGenerator0 archiveGenerator409),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator389)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator367))))] (
  .cons [archiveGenerator418,
      archiveGenerator417,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator386))] (
  .cons [(.mul archiveGenerator0 archiveGenerator407)] (
  .cons [(.mul archiveGenerator7 archiveGenerator267),
      (.mul archiveGenerator1 archiveGenerator385)] (
  .cons [(.mul archiveGenerator7 archiveGenerator266),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator267))] (
  .cons [(.mul archiveGenerator2 archiveGenerator359)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator75))),
      (.mul archiveGenerator1 archiveGenerator383),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator359))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator67))),
      (.mul archiveGenerator2 archiveGenerator355),
      (.mul archiveGenerator0 archiveGenerator405),
      (.mul archiveGenerator0 (.mul archiveGenerator20 archiveGenerator188))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator255)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator346)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator359)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator349)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator358))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator188)))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator404),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator347)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator380))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300))))))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator138)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator138))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator244)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator137)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator403)] (
  .cons [(.mul archiveGenerator0 archiveGenerator402)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator200))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator253))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator252)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator183)))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator416] (
  .cons [(.mul archiveGenerator1 archiveGenerator379)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows137 : BasisRows generators 137 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator430] (
  .cons [archiveGenerator429,
      (.mul archiveGenerator69 archiveGenerator95)] (
  .cons [(.mul archiveGenerator2 archiveGenerator376),
      (.mul archiveGenerator1 archiveGenerator415),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator69)))] (
  .cons [archiveGenerator428,
      (.mul archiveGenerator3 archiveGenerator333),
      (.mul archiveGenerator2 archiveGenerator373),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator375)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator415)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))] (
  .cons [archiveGenerator427,
      (.mul archiveGenerator1 archiveGenerator413),
      (.mul archiveGenerator1 archiveGenerator412),
      (.mul archiveGenerator0 archiveGenerator419),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator414)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))))))))))] (
  .cons [archiveGenerator426,
      archiveGenerator425,
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator89)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator391))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator375))))] (
  .cons [(.mul archiveGenerator76 archiveGenerator82),
      (.mul archiveGenerator9 archiveGenerator251),
      (.mul archiveGenerator7 archiveGenerator275),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator367)))))] (
  .cons [(.mul archiveGenerator23 archiveGenerator181),
      (.mul archiveGenerator0 archiveGenerator418),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator386)))] (
  .cons [archiveGenerator424,
      archiveGenerator423] (
  .cons [archiveGenerator422,
      (.mul archiveGenerator8 archiveGenerator261),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator267))] (
  .cons [archiveGenerator421,
      (.mul archiveGenerator17 archiveGenerator209),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator267)))] (
  .cons [(.mul archiveGenerator16 archiveGenerator209),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator359))] (
  .cons [archiveGenerator420] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator255))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator359))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator349))))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator248),
      (.mul archiveGenerator8 archiveGenerator260)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator167)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator188))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator180)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator347))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator259),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator380)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator258)] (
  .cons [(.mul archiveGenerator17 archiveGenerator206),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317)))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator257),
      (.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator137)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300)))))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator137))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator402),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator403))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator402))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator253)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator252))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator183))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator416)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows138 : BasisRows generators 138 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator324))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator341),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator69))))] (
  .cons [archiveGenerator446,
      (.mul archiveGenerator3 archiveGenerator340),
      (.mul archiveGenerator2 archiveGenerator400)] (
  .cons [(.mul archiveGenerator3 archiveGenerator339),
      (.mul archiveGenerator2 archiveGenerator398)] (
  .cons [archiveGenerator445,
      (.mul archiveGenerator2 archiveGenerator396)] (
  .cons [archiveGenerator444,
      archiveGenerator443,
      (.mul archiveGenerator0 archiveGenerator429),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator95))] (
  .cons [archiveGenerator442,
      archiveGenerator441,
      (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator82)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator68 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator428),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator333)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator373)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))] (
  .cons [(.mul archiveGenerator25 archiveGenerator190),
      (.mul archiveGenerator3 archiveGenerator336),
      (.mul archiveGenerator0 archiveGenerator427),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator419)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69)))))))))))] (
  .cons [(.mul archiveGenerator24 archiveGenerator190),
      (.mul archiveGenerator3 archiveGenerator335),
      (.mul archiveGenerator0 archiveGenerator425),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator391)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator375)))))] (
  .cons [archiveGenerator440,
      archiveGenerator439,
      (.mul archiveGenerator23 archiveGenerator190),
      (.mul archiveGenerator1 archiveGenerator418),
      (.mul archiveGenerator1 archiveGenerator417)] (
  .cons [archiveGenerator438,
      (.mul archiveGenerator7 archiveGenerator279),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator418))] (
  .cons [archiveGenerator437,
      (.mul archiveGenerator23 archiveGenerator189),
      (.mul archiveGenerator0 archiveGenerator424)] (
  .cons [archiveGenerator436,
      (.mul archiveGenerator23 archiveGenerator188),
      (.mul archiveGenerator0 archiveGenerator422),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator267)))] (
  .cons [(.mul archiveGenerator22 archiveGenerator188),
      (.mul archiveGenerator8 archiveGenerator267),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator209))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator188)),
      (.mul archiveGenerator7 archiveGenerator278),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator209))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator187)),
      (.mul archiveGenerator2 archiveGenerator381)] (
  .cons [archiveGenerator435,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))] (
  .cons [archiveGenerator434,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator33)))),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator101)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator186)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator260))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator80)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator127)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator72))))] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator113)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator32)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator147)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator185)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator42))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator184)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator23)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16))))))] (
  .cons [archiveGenerator433,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator125)))] (
  .cons [archiveGenerator432,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator50))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator403)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator265),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator402)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator111))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator183))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator182))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))))))))))))] (
  .cons [archiveGenerator431] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator416))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows139 : BasisRows generators 139 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator4 archiveGenerator324)] (
  .cons [(.mul archiveGenerator4 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator69)))))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator76)),
      (.mul archiveGenerator0 archiveGenerator446),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator340))] (
  .cons [archiveGenerator451,
      (.mul archiveGenerator2 (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator76))),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator339)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator398))] (
  .cons [(.mul archiveGenerator3 archiveGenerator352),
      (.mul archiveGenerator1 (.mul archiveGenerator69 archiveGenerator95)),
      (.mul archiveGenerator0 archiveGenerator445)] (
  .cons [archiveGenerator450,
      (.mul archiveGenerator0 archiveGenerator443),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator429))] (
  .cons [(.mul archiveGenerator18 archiveGenerator209),
      (.mul archiveGenerator0 archiveGenerator442),
      (.mul archiveGenerator0 archiveGenerator441)] (
  .cons [(.mul archiveGenerator1 archiveGenerator427),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator428)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))] (
  .cons [(.mul archiveGenerator1 archiveGenerator426),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator336)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))))))))))))] (
  .cons [archiveGenerator449,
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator275)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator425))] (
  .cons [archiveGenerator448,
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator287)),
      (.mul archiveGenerator0 archiveGenerator440),
      (.mul archiveGenerator0 archiveGenerator439)] (
  .cons [(.mul archiveGenerator1 archiveGenerator424),
      (.mul archiveGenerator0 archiveGenerator438),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator418)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator76))),
      (.mul archiveGenerator0 archiveGenerator437)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator75))),
      (.mul archiveGenerator0 (.mul archiveGenerator23 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator422))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator22 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator267)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator209)))] (
  .cons [archiveGenerator447,
      (.mul archiveGenerator1 archiveGenerator420),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator278))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator187)))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator434)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator260)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator147))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator317)))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator185))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator300)))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator184)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator433)] (
  .cons [(.mul archiveGenerator0 archiveGenerator432)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator402))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator403))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator402))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator183)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator182)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator431)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows140 : BasisRows generators 140 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator69))))] (
  .cons [archiveGenerator468] (
  .cons [archiveGenerator467,
      (.mul archiveGenerator3 archiveGenerator368),
      (.mul archiveGenerator1 archiveGenerator446)] (
  .cons [archiveGenerator466,
      archiveGenerator465,
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator368)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator446)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator340)))] (
  .cons [archiveGenerator464,
      (.mul archiveGenerator69 archiveGenerator107),
      (.mul archiveGenerator3 archiveGenerator367),
      (.mul archiveGenerator1 archiveGenerator445),
      (.mul archiveGenerator0 archiveGenerator451)] (
  .cons [archiveGenerator463,
      (.mul archiveGenerator18 archiveGenerator213),
      (.mul archiveGenerator3 archiveGenerator366),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator352)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator445))] (
  .cons [archiveGenerator462,
      archiveGenerator461,
      (.mul archiveGenerator69 archiveGenerator104),
      (.mul archiveGenerator1 archiveGenerator442),
      (.mul archiveGenerator0 archiveGenerator450),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator443))] (
  .cons [archiveGenerator460,
      archiveGenerator459,
      (.mul archiveGenerator76 archiveGenerator95),
      (.mul archiveGenerator3 archiveGenerator365),
      (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator209))] (
  .cons [archiveGenerator458,
      (.mul archiveGenerator13 archiveGenerator251),
      (.mul archiveGenerator3 archiveGenerator363),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator428))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))] (
  .cons [archiveGenerator457,
      (.mul archiveGenerator68 archiveGenerator107),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator335)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69)))))))))))))] (
  .cons [archiveGenerator456,
      (.mul archiveGenerator67 archiveGenerator107),
      (.mul archiveGenerator1 archiveGenerator439),
      (.mul archiveGenerator0 archiveGenerator449),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator425)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator261),
      (.mul archiveGenerator1 archiveGenerator438),
      (.mul archiveGenerator0 archiveGenerator448),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator439))] (
  .cons [(.mul archiveGenerator8 archiveGenerator280),
      (.mul archiveGenerator3 archiveGenerator359),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator438)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator418))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator279),
      (.mul archiveGenerator1 archiveGenerator436),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator437))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator422)))] (
  .cons [archiveGenerator455,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator267))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator209))))] (
  .cons [archiveGenerator454,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator150)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator188))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator248),
      (.mul archiveGenerator8 archiveGenerator278),
      (.mul archiveGenerator1 archiveGenerator435)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator167))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator194))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator193)),
      (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator64))] (
  .cons [(.mul archiveGenerator8 archiveGenerator277)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator149))] (
  .cons [archiveGenerator453] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator185))))] (
  .cons [archiveGenerator452] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator433))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator432))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator403)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator402)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator183))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator182))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator431),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator431))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows141 : BasisRows generators 141 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator4 archiveGenerator324))] (
  .cons [(.mul archiveGenerator3 archiveGenerator378),
      (.mul archiveGenerator1 (.mul archiveGenerator4 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator377)] (
  .cons [archiveGenerator480,
      (.mul archiveGenerator1 (.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator76)))] (
  .cons [archiveGenerator479,
      (.mul archiveGenerator3 archiveGenerator376),
      (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator95)),
      (.mul archiveGenerator0 archiveGenerator465),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator446)))] (
  .cons [archiveGenerator478,
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator376)),
      (.mul archiveGenerator0 archiveGenerator464),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator451))] (
  .cons [archiveGenerator477,
      (.mul archiveGenerator1 archiveGenerator450)] (
  .cons [archiveGenerator476,
      (.mul archiveGenerator0 archiveGenerator462),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator450))] (
  .cons [archiveGenerator475,
      archiveGenerator474,
      (.mul archiveGenerator0 archiveGenerator460),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator365))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator251)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator363)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator107)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))))))))))))))] (
  .cons [archiveGenerator473,
      (.mul archiveGenerator1 archiveGenerator448),
      (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator107)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449))] (
  .cons [archiveGenerator472,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator448)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator439)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator267),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator359)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator418)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator437)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator201)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator422))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80))),
      (.mul archiveGenerator1 archiveGenerator447),
      (.mul archiveGenerator0 archiveGenerator455),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator209)))))] (
  .cons [archiveGenerator471,
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))),
      (.mul archiveGenerator0 archiveGenerator454)] (
  .cons [(.mul archiveGenerator64 archiveGenerator113),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator80))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator278))] (
  .cons [(.mul archiveGenerator64 archiveGenerator112),
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator80)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator79))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator154)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator32)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator154)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator46)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator45)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20))))))] (
  .cons [(.mul archiveGenerator17 archiveGenerator225),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19))))))] (
  .cons [(.mul archiveGenerator16 archiveGenerator225),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator136))),
      (.mul archiveGenerator0 archiveGenerator452)] (
  .cons [(.mul archiveGenerator16 archiveGenerator224),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator56))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator78))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator77))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator283),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator432)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator153))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator200)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator403))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator199)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator402))))))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator470] (
  .cons [archiveGenerator469] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows142 : BasisRows generators 142 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator324),
      (.mul archiveGenerator3 archiveGenerator400)] (
  .cons [(.mul archiveGenerator5 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator3 archiveGenerator399),
      (.mul archiveGenerator3 archiveGenerator398),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator378))] (
  .cons [(.mul archiveGenerator3 archiveGenerator397),
      (.mul archiveGenerator3 archiveGenerator396),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator446)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator377))] (
  .cons [(.mul archiveGenerator3 archiveGenerator394),
      (.mul archiveGenerator3 archiveGenerator392),
      (.mul archiveGenerator2 archiveGenerator445),
      (.mul archiveGenerator0 archiveGenerator480)] (
  .cons [(.mul archiveGenerator3 archiveGenerator391),
      (.mul archiveGenerator3 archiveGenerator390),
      (.mul archiveGenerator0 archiveGenerator479),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator95))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator446))))] (
  .cons [archiveGenerator486,
      archiveGenerator485,
      (.mul archiveGenerator3 archiveGenerator389),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator451)))] (
  .cons [archiveGenerator484,
      (.mul archiveGenerator3 archiveGenerator386),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator442))] (
  .cons [archiveGenerator483,
      (.mul archiveGenerator1 archiveGenerator459)] (
  .cons [archiveGenerator482,
      (.mul archiveGenerator69 archiveGenerator113),
      (.mul archiveGenerator0 archiveGenerator475),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator460))] (
  .cons [archiveGenerator481,
      (.mul archiveGenerator69 archiveGenerator112),
      (.mul archiveGenerator2 archiveGenerator439),
      (.mul archiveGenerator1 archiveGenerator457),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator439)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator68 archiveGenerator107))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69)))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator67 archiveGenerator107))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator472),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator95))),
      (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator267)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator359))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator418))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator83))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator437))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator201))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator422)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator209))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator471),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator454))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator113)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator278)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator112))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator64 archiveGenerator64)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator453),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator452),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator225))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator225)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator452))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator224))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator403)))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator402)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator470)] (
  .cons [(.mul archiveGenerator0 archiveGenerator469)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator431))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246))))))))))))))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows143 : BasisRows generators 143 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator398))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator397)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator396))] (
  .cons [(.mul archiveGenerator7 archiveGenerator314),
      (.mul archiveGenerator1 archiveGenerator479),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator392)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator445)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator480))] (
  .cons [(.mul archiveGenerator7 archiveGenerator311),
      (.mul archiveGenerator3 archiveGenerator412),
      (.mul archiveGenerator2 archiveGenerator450),
      (.mul archiveGenerator1 archiveGenerator478),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator391)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator390)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator479)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator446)))))] (
  .cons [archiveGenerator497,
      (.mul archiveGenerator1 archiveGenerator477),
      (.mul archiveGenerator0 archiveGenerator486),
      (.mul archiveGenerator0 archiveGenerator485),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator389)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator451))))] (
  .cons [archiveGenerator496,
      (.mul archiveGenerator76 archiveGenerator107),
      (.mul archiveGenerator0 archiveGenerator484),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator386))] (
  .cons [(.mul archiveGenerator74 archiveGenerator107),
      (.mul archiveGenerator9 archiveGenerator281),
      (.mul archiveGenerator3 archiveGenerator407),
      (.mul archiveGenerator0 archiveGenerator483)] (
  .cons [archiveGenerator495,
      (.mul archiveGenerator13 archiveGenerator262),
      (.mul archiveGenerator0 archiveGenerator482),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator113)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator475))] (
  .cons [archiveGenerator494,
      (.mul archiveGenerator13 archiveGenerator261),
      (.mul archiveGenerator0 archiveGenerator481),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator112)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator439)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))] (
  .cons [archiveGenerator493,
      (.mul archiveGenerator8 archiveGenerator294),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator448)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator69))))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator293),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440)))))] (
  .cons [archiveGenerator492] (
  .cons [(.mul archiveGenerator8 archiveGenerator292),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator188))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator291),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator422))))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator167))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator194))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator208)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator113)))] (
  .cons [archiveGenerator491,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator207))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator160))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator206))] (
  .cons [archiveGenerator490] (
  .cons [archiveGenerator489] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138)))))] (
  .cons [archiveGenerator488] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator225)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator225))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator452)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator224)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator403))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator402))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator470))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator469))] (
  .cons [archiveGenerator487] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator246)))))))))))))))))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows144 : BasisRows generators 144 0 :=
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator7 archiveGenerator324)] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator324))] (
  .cons [archiveGenerator508] (
  .cons [archiveGenerator507,
      archiveGenerator506] (
  .cons [archiveGenerator505,
      (.mul archiveGenerator6 archiveGenerator324)] (
  .cons [(.mul archiveGenerator6 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator3 (.mul archiveGenerator69 archiveGenerator93)),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator324))] (
  .cons [(.mul archiveGenerator7 archiveGenerator323),
      (.mul archiveGenerator1 (.mul archiveGenerator5 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [archiveGenerator504,
      (.mul archiveGenerator2 archiveGenerator465)] (
  .cons [(.mul archiveGenerator7 archiveGenerator322)] (
  .cons [archiveGenerator503,
      (.mul archiveGenerator7 archiveGenerator321),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator314))] (
  .cons [(.mul archiveGenerator1 archiveGenerator486),
      (.mul archiveGenerator1 archiveGenerator485),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator311)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator391))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator446))))))] (
  .cons [archiveGenerator502,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator486)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator485)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator389)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator288),
      (.mul archiveGenerator7 archiveGenerator319),
      (.mul archiveGenerator3 archiveGenerator417),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator484))] (
  .cons [(.mul archiveGenerator23 archiveGenerator213),
      (.mul archiveGenerator0 (.mul archiveGenerator74 archiveGenerator107)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator407))] (
  .cons [(.mul archiveGenerator0 archiveGenerator495),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator482)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator113))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator475)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator268),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator481)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator112))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator439))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))] (
  .cons [archiveGenerator501,
      archiveGenerator500,
      (.mul archiveGenerator13 archiveGenerator267),
      (.mul archiveGenerator9 archiveGenerator286)] (
  .cons [(.mul archiveGenerator13 archiveGenerator266),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440))))))] (
  .cons [] (
  .cons [archiveGenerator499,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator292))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator24)))),
      (.mul archiveGenerator8 archiveGenerator299),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator80))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator291))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator64)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator89)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator80))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator89))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator162)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))),
      (.mul archiveGenerator0 archiveGenerator491)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator113))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator147))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator51)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator146))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator23))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator22)))))),
      (.mul archiveGenerator0 archiveGenerator489)] (
  .cons [(.mul archiveGenerator17 archiveGenerator238),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator8)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator298),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator88)))),
      (.mul archiveGenerator0 archiveGenerator488)] (
  .cons [(.mul archiveGenerator8 archiveGenerator297),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator17))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator452))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator50))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator225))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator49))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator452))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator211))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator145)))] (
  .cons [archiveGenerator498] (
  .cons [] (
  .cons [(.mul archiveGenerator8 archiveGenerator296)] (
  .cons [(.mul archiveGenerator8 archiveGenerator295)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator469)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows145 : BasisRows generators 145 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator508)] (
  .cons [(.mul archiveGenerator0 archiveGenerator507),
      (.mul archiveGenerator0 archiveGenerator506)] (
  .cons [(.mul archiveGenerator0 archiveGenerator505),
      (.mul archiveGenerator0 (.mul archiveGenerator6 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator6 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [archiveGenerator514,
      archiveGenerator513] (
  .cons [archiveGenerator512,
      (.mul archiveGenerator7 archiveGenerator333),
      (.mul archiveGenerator2 archiveGenerator479),
      (.mul archiveGenerator0 archiveGenerator504)] (
  .cons [(.mul archiveGenerator3 archiveGenerator428),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator333)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator322))] (
  .cons [archiveGenerator511,
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator412)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator314)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator314),
      (.mul archiveGenerator3 archiveGenerator425),
      (.mul archiveGenerator1 archiveGenerator497),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator311)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator312),
      (.mul archiveGenerator1 (.mul archiveGenerator76 archiveGenerator107)),
      (.mul archiveGenerator0 archiveGenerator502)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator69)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator319)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator484)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator328),
      (.mul archiveGenerator1 archiveGenerator495)] (
  .cons [(.mul archiveGenerator2 archiveGenerator473),
      (.mul archiveGenerator1 archiveGenerator494),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator482)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator164)),
      (.mul archiveGenerator1 archiveGenerator493),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator481))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator112)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator95))),
      (.mul archiveGenerator0 archiveGenerator500)] (
  .cons [archiveGenerator510,
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator212))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440)))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator347),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator292)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator299)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator291)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator64)))] (
  .cons [] (
  .cons [archiveGenerator509,
      (.mul archiveGenerator1 archiveGenerator491)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator491))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator238))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator298)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator488))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator297))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator225)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator452)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator296))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator295))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator487)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows146 : BasisRows generators 146 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator324))] (
  .cons [archiveGenerator527,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator324)))] (
  .cons [archiveGenerator526,
      (.mul archiveGenerator8 archiveGenerator324),
      (.mul archiveGenerator1 archiveGenerator508)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator1 archiveGenerator507),
      (.mul archiveGenerator1 archiveGenerator506),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator508))] (
  .cons [archiveGenerator525,
      (.mul archiveGenerator1 archiveGenerator505),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator507)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator506))] (
  .cons [archiveGenerator524,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator505)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator6 archiveGenerator324)))] (
  .cons [archiveGenerator523,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator6 (.mul archiveGenerator69 archiveGenerator69))))] (
  .cons [archiveGenerator522,
      archiveGenerator521,
      (.mul archiveGenerator1 archiveGenerator504),
      (.mul archiveGenerator0 archiveGenerator514),
      (.mul archiveGenerator0 archiveGenerator513)] (
  .cons [archiveGenerator520,
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator322)),
      (.mul archiveGenerator0 archiveGenerator512),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator333)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator479)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator504))] (
  .cons [(.mul archiveGenerator2 archiveGenerator486),
      (.mul archiveGenerator1 archiveGenerator503),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator321)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator428)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator333)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator335),
      (.mul archiveGenerator2 archiveGenerator484),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator486)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator485)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator314))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator281),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator335)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator314)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator425)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator311))))] (
  .cons [(.mul archiveGenerator2 archiveGenerator482),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator319)),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator417)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator312)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator502))] (
  .cons [(.mul archiveGenerator3 archiveGenerator438),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator319))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator484))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator294),
      (.mul archiveGenerator3 archiveGenerator437)] (
  .cons [archiveGenerator519,
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator482))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator293),
      (.mul archiveGenerator1 archiveGenerator501),
      (.mul archiveGenerator1 archiveGenerator500),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator481)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator318),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500))] (
  .cons [archiveGenerator518,
      (.mul archiveGenerator9 archiveGenerator292),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449)))))))] (
  .cons [archiveGenerator517,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator168)),
      (.mul archiveGenerator8 archiveGenerator316),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator167))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator194))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator219)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator299)))] (
  .cons [archiveGenerator516,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator218))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator167))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator149))),
      (.mul archiveGenerator0 archiveGenerator509)] (
  .cons [(.mul archiveGenerator8 archiveGenerator315),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator491)))] (
  .cons [(.mul archiveGenerator16 archiveGenerator245)] (
  .cons [(.mul archiveGenerator17 archiveGenerator244)] (
  .cons [(.mul archiveGenerator16 archiveGenerator244)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator298))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator488)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator297)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator225))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator452))))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator498)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator296)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator295)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator515] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows147 : BasisRows generators 147 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator526),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator508)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator353),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator507))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator506)))] (
  .cons [archiveGenerator535,
      (.mul archiveGenerator7 archiveGenerator352),
      (.mul archiveGenerator0 archiveGenerator524),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator505)))] (
  .cons [(.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator352)),
      (.mul archiveGenerator1 archiveGenerator513),
      (.mul archiveGenerator0 archiveGenerator523)] (
  .cons [(.mul archiveGenerator0 archiveGenerator521),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator513))] (
  .cons [archiveGenerator534,
      (.mul archiveGenerator43 archiveGenerator174),
      (.mul archiveGenerator7 archiveGenerator351),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator333)))] (
  .cons [archiveGenerator533,
      archiveGenerator532,
      (.mul archiveGenerator8 archiveGenerator333),
      (.mul archiveGenerator1 archiveGenerator511),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator486))] (
  .cons [archiveGenerator531,
      (.mul archiveGenerator13 archiveGenerator288),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator484)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator314)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator425))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator311)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator312)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator287),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator69)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator484)))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator286),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator437))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator482)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator481))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))))] (
  .cons [archiveGenerator530,
      (.mul archiveGenerator1 archiveGenerator510),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500)))] (
  .cons [(.mul archiveGenerator17 archiveGenerator255),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101))),
      (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator292)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator327),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator316)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440)))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator72)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator101))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator347))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator80))))] (
  .cons [archiveGenerator529,
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator101))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator64))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))),
      (.mul archiveGenerator0 archiveGenerator516)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator154))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator491))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator64)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator51))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator509))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator64)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator23)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator491))))] (
  .cons [(.mul archiveGenerator59 archiveGenerator137),
      (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator29))))))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator138)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator9))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator244))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator225)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator100)))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator244))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator224)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator40)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator56)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator55)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator223))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator117)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator153)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator152)))] (
  .cons [archiveGenerator528] (
  .cons [(.mul archiveGenerator17 archiveGenerator253)] (
  .cons [(.mul archiveGenerator8 archiveGenerator326)] (
  .cons [(.mul archiveGenerator8 archiveGenerator325)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows148 : BasisRows generators 148 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator324))] (
  .cons [archiveGenerator548,
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator527)] (
  .cons [(.mul archiveGenerator2 archiveGenerator506),
      (.mul archiveGenerator1 (.mul archiveGenerator8 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator324)))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator368),
      (.mul archiveGenerator1 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator69))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator506)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator526)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator324)))] (
  .cons [archiveGenerator547,
      archiveGenerator546,
      (.mul archiveGenerator1 archiveGenerator525),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator69))))] (
  .cons [archiveGenerator545,
      (.mul archiveGenerator7 archiveGenerator367),
      (.mul archiveGenerator1 archiveGenerator524),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator506))))] (
  .cons [archiveGenerator544,
      (.mul archiveGenerator7 archiveGenerator366),
      (.mul archiveGenerator1 archiveGenerator523),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator352)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator524))] (
  .cons [archiveGenerator543,
      (.mul archiveGenerator3 archiveGenerator463),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator352))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator523))] (
  .cons [archiveGenerator542,
      archiveGenerator541,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator521))] (
  .cons [archiveGenerator540,
      (.mul archiveGenerator8 archiveGenerator338),
      (.mul archiveGenerator0 archiveGenerator534),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator174)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator351)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator333))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator337),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator363)),
      (.mul archiveGenerator0 archiveGenerator533),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator333)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator486)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator72)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator314))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator311))))))] (
  .cons [] (
  .cons [archiveGenerator539] (
  .cons [(.mul archiveGenerator1 archiveGenerator519),
      (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator286))] (
  .cons [archiveGenerator538,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator75))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator482))))))] (
  .cons [archiveGenerator537,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator105))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator481)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator530),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator292))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator449)))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator316))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440))))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator529)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator516))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator509)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator491)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator138))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator244)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator225))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator244)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator224)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator253))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator326))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator325))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator536] (
  .cons [(.mul archiveGenerator1 archiveGenerator515)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows149 : BasisRows generators 149 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator324),
      (.mul archiveGenerator0 archiveGenerator548)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator7 archiveGenerator378)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator506)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator324))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator526)))] (
  .cons [(.mul archiveGenerator69 archiveGenerator134),
      (.mul archiveGenerator3 archiveGenerator480),
      (.mul archiveGenerator0 archiveGenerator546)] (
  .cons [(.mul archiveGenerator69 archiveGenerator133),
      (.mul archiveGenerator1 archiveGenerator535),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator367)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator506)))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator513)),
      (.mul archiveGenerator0 archiveGenerator544),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator366)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator524)))] (
  .cons [(.mul archiveGenerator7 archiveGenerator371),
      (.mul archiveGenerator3 archiveGenerator477),
      (.mul archiveGenerator0 archiveGenerator543)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator521)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator533),
      (.mul archiveGenerator0 archiveGenerator540),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator338)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator534))] (
  .cons [(.mul archiveGenerator8 archiveGenerator351),
      (.mul archiveGenerator1 archiveGenerator531),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator337)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator363))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator533)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator333)))] (
  .cons [archiveGenerator552,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator181)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator72))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator314)))))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator294),
      (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator328))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator209)),
      (.mul archiveGenerator1 (.mul archiveGenerator13 archiveGenerator287))] (
  .cons [(.mul archiveGenerator8 archiveGenerator350),
      (.mul archiveGenerator0 archiveGenerator539)] (
  .cons [archiveGenerator551,
      (.mul archiveGenerator8 archiveGenerator348)] (
  .cons [archiveGenerator550,
      (.mul archiveGenerator13 archiveGenerator292)] (
  .cons [(.mul archiveGenerator8 archiveGenerator347),
      (.mul archiveGenerator8 archiveGenerator346),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))))))] (
  .cons [archiveGenerator549,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator194))] (
  .cons [(.mul archiveGenerator17 archiveGenerator260),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator219)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator440)))))))))))] (
  .cons [(.mul archiveGenerator16 archiveGenerator260),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator233))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator232))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator160)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator345),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator516)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator344)] (
  .cons [(.mul archiveGenerator17 archiveGenerator257),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator509))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator343),
      (.mul archiveGenerator1 (.mul archiveGenerator59 archiveGenerator137)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator491))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator244))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator225))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator224))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator402)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator326)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator325)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator536)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows150 : BasisRows generators 150 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator11 archiveGenerator324)] (
  .cons [(.mul archiveGenerator10 archiveGenerator324),
      (.mul archiveGenerator2 archiveGenerator527),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator324))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator400),
      (.mul archiveGenerator2 archiveGenerator526),
      (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator548))] (
  .cons [(.mul archiveGenerator7 archiveGenerator398),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator400)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator8 archiveGenerator324))),
      (.mul archiveGenerator0 (.mul archiveGenerator9 (.mul archiveGenerator69 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator378))] (
  .cons [archiveGenerator567,
      archiveGenerator566,
      (.mul archiveGenerator7 archiveGenerator396),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator398)),
      (.mul archiveGenerator2 archiveGenerator525),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator69)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator324)))))))] (
  .cons [archiveGenerator565,
      (.mul archiveGenerator7 archiveGenerator394),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator396)),
      (.mul archiveGenerator2 archiveGenerator524),
      (.mul archiveGenerator1 archiveGenerator547),
      (.mul archiveGenerator1 archiveGenerator546),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator526))))] (
  .cons [archiveGenerator564,
      archiveGenerator563,
      (.mul archiveGenerator2 archiveGenerator523),
      (.mul archiveGenerator1 archiveGenerator545),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator480)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator546))] (
  .cons [archiveGenerator562,
      (.mul archiveGenerator43 archiveGenerator191),
      (.mul archiveGenerator2 archiveGenerator521),
      (.mul archiveGenerator1 archiveGenerator544),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator367)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator367),
      (.mul archiveGenerator3 archiveGenerator485),
      (.mul archiveGenerator1 archiveGenerator543),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator544)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator366)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator366),
      (.mul archiveGenerator3 archiveGenerator484),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator371)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator543))] (
  .cons [(.mul archiveGenerator43 archiveGenerator189),
      (.mul archiveGenerator1 archiveGenerator540)] (
  .cons [(.mul archiveGenerator9 archiveGenerator331),
      (.mul archiveGenerator7 archiveGenerator385),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator540))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator190)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator337))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator533)))] (
  .cons [archiveGenerator561] (
  .cons [archiveGenerator560,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator189))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator188)),
      (.mul archiveGenerator9 archiveGenerator328)] (
  .cons [(.mul archiveGenerator13 archiveGenerator303),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator539))] (
  .cons [(.mul archiveGenerator42 archiveGenerator187),
      (.mul archiveGenerator17 archiveGenerator267),
      (.mul archiveGenerator0 archiveGenerator551)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator292))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))),
      (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator188)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator346)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator52)))),
      (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator187)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator101))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500))))))] (
  .cons [archiveGenerator559,
      archiveGenerator558,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator80))))] (
  .cons [archiveGenerator557,
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator101)))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator260))] (
  .cons [(.mul archiveGenerator64 archiveGenerator138),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator113))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator260))] (
  .cons [(.mul archiveGenerator64 archiveGenerator137),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator162))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator113)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator51)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator112)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator23))))))] (
  .cons [(.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator147)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator32))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator185)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator13))))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator509)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator238)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator60))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator491)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator237)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator17)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator17)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator244)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator31))))))] (
  .cons [archiveGenerator556,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator161)))] (
  .cons [archiveGenerator555,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator50))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator111))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator110))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator354)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator183))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator183))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator236))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator554] (
  .cons [archiveGenerator553] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator536))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows151 : BasisRows generators 151 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator10 archiveGenerator324))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator526)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator18 archiveGenerator264),
      (.mul archiveGenerator12 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator398)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 (.mul archiveGenerator69 archiveGenerator69))))] (
  .cons [(.mul archiveGenerator12 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator7 archiveGenerator415),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator396)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator398))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator324))))))))] (
  .cons [archiveGenerator571,
      (.mul archiveGenerator7 archiveGenerator414),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator394)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator524)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator526)))))] (
  .cons [archiveGenerator570,
      (.mul archiveGenerator7 archiveGenerator412),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator523)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator546)))] (
  .cons [archiveGenerator569,
      (.mul archiveGenerator0 archiveGenerator562),
      (.mul archiveGenerator0 (.mul archiveGenerator43 archiveGenerator191)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator521))] (
  .cons [(.mul archiveGenerator8 archiveGenerator373),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator477)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator367)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator485))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator80)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator366)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator484))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator79))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator540)))] (
  .cons [archiveGenerator568,
      (.mul archiveGenerator1 archiveGenerator552),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator533))))] (
  .cons [(.mul archiveGenerator69 archiveGenerator138),
      (.mul archiveGenerator0 archiveGenerator561)] (
  .cons [(.mul archiveGenerator18 archiveGenerator260),
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator76)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator75)))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator267))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator188))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator292)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator549),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator346))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500)))))))] (
  .cons [(.mul archiveGenerator0 archiveGenerator558)] (
  .cons [(.mul archiveGenerator0 archiveGenerator557),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator137))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator185))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator509))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator238))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator491))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator237))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator244))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator556)] (
  .cons [(.mul archiveGenerator0 archiveGenerator555)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator402))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator183)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator236)))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator554)] (
  .cons [(.mul archiveGenerator0 archiveGenerator553)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows152 : BasisRows generators 152 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator324),
      (.mul archiveGenerator2 archiveGenerator548)] (
  .cons [(.mul archiveGenerator3 archiveGenerator506)] (
  .cons [] (
  .cons [archiveGenerator577,
      (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator368)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 archiveGenerator324))))] (
  .cons [archiveGenerator576,
      (.mul archiveGenerator1 archiveGenerator566),
      (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator264)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator9 (.mul archiveGenerator69 archiveGenerator69)))))] (
  .cons [(.mul archiveGenerator3 archiveGenerator504),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator546)),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator415)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator396)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator69 archiveGenerator75)),
      (.mul archiveGenerator2 archiveGenerator544),
      (.mul archiveGenerator1 archiveGenerator563),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator414)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator394)))] (
  .cons [archiveGenerator575,
      (.mul archiveGenerator2 archiveGenerator543),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator544)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator546))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator485)),
      (.mul archiveGenerator0 archiveGenerator569),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator562))] (
  .cons [(.mul archiveGenerator2 archiveGenerator540),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator367))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator485)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator43 archiveGenerator189)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator540)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator80))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator366))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator484)))] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator267)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator385)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator79)))] (
  .cons [(.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator266)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator540))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator209)),
      (.mul archiveGenerator1 archiveGenerator561),
      (.mul archiveGenerator0 archiveGenerator568),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator533)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator384),
      (.mul archiveGenerator1 archiveGenerator560),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator138)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator561))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator250)),
      (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator260))] (
  .cons [(.mul archiveGenerator8 archiveGenerator383),
      (.mul archiveGenerator2 archiveGenerator538)] (
  .cons [(.mul archiveGenerator9 archiveGenerator346),
      (.mul archiveGenerator8 archiveGenerator382),
      (.mul archiveGenerator2 archiveGenerator537),
      (.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator187))] (
  .cons [archiveGenerator574,
      (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator150))] (
  .cons [archiveGenerator573,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator194))] (
  .cons [(.mul archiveGenerator17 archiveGenerator278),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator219)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator380),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator248)),
      (.mul archiveGenerator1 archiveGenerator558),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator167))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator558))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator166))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator247)),
      (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator137)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator245)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator137)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator149))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator244))] (
  .cons [archiveGenerator572] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator238))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator138)))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator556))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator555))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator183))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator236))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator553),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator554))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator553))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows153 : BasisRows generators 153 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator324))] (
  .cons [archiveGenerator584,
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator506))] (
  .cons [(.mul archiveGenerator7 archiveGenerator430)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator12 archiveGenerator324)),
      (.mul archiveGenerator0 archiveGenerator577)] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator69 archiveGenerator134)),
      (.mul archiveGenerator1 (.mul archiveGenerator12 (.mul archiveGenerator69 archiveGenerator69))),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator415))] (
  .cons [archiveGenerator583,
      (.mul archiveGenerator1 archiveGenerator571),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator504)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator415)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator415),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator412)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator544)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator414)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator414),
      (.mul archiveGenerator7 archiveGenerator425),
      (.mul archiveGenerator0 archiveGenerator575),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator546)))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator332),
      (.mul archiveGenerator4 archiveGenerator486),
      (.mul archiveGenerator3 (.mul archiveGenerator3 archiveGenerator425)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator562)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator331)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator80))))] (
  .cons [archiveGenerator582,
      (.mul archiveGenerator0 (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator267)))] (
  .cons [archiveGenerator581] (
  .cons [(.mul archiveGenerator13 archiveGenerator328),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator568))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator212)),
      (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator260)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator138)))] (
  .cons [(.mul archiveGenerator20 archiveGenerator267),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator188))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator80))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator255))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator254))] (
  .cons [archiveGenerator580,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))),
      (.mul archiveGenerator0 archiveGenerator573)] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 archiveGenerator404),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator101)))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator278)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator147),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator173))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator380)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500)))))))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator146),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator80)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator558)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator51))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator118)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator260)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator23)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator64))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator42 archiveGenerator137)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator32)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator137))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator138))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator13)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator138))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator63)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator137))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator20))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator40))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator39))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator403),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator171)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator402),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator78))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator117))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator116))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator401),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator555)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator200))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator253))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator252))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator579] (
  .cons [archiveGenerator578] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator554)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows154 : BasisRows generators 154 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator11 archiveGenerator324))] (
  .cons [archiveGenerator593,
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator527)),
      (.mul archiveGenerator1 (.mul archiveGenerator13 archiveGenerator324))] (
  .cons [archiveGenerator592,
      (.mul archiveGenerator7 archiveGenerator446),
      (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator400)),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator506)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator341),
      (.mul archiveGenerator3 archiveGenerator525),
      (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator398)),
      (.mul archiveGenerator0 archiveGenerator584),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator506)))] (
  .cons [(.mul archiveGenerator3 archiveGenerator524),
      (.mul archiveGenerator2 archiveGenerator566),
      (.mul archiveGenerator2 (.mul archiveGenerator7 archiveGenerator396)),
      (.mul archiveGenerator1 archiveGenerator577)] (
  .cons [(.mul archiveGenerator14 archiveGenerator324),
      (.mul archiveGenerator3 archiveGenerator523),
      (.mul archiveGenerator2 archiveGenerator565),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator577))] (
  .cons [archiveGenerator591,
      (.mul archiveGenerator3 archiveGenerator521),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator504))] (
  .cons [archiveGenerator590,
      (.mul archiveGenerator0 archiveGenerator583),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator504)))] (
  .cons [archiveGenerator589,
      (.mul archiveGenerator9 archiveGenerator373),
      (.mul archiveGenerator1 archiveGenerator575),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator415))] (
  .cons [(.mul archiveGenerator8 archiveGenerator419),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator414)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator575))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator69 archiveGenerator89)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator562))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator335)] (
  .cons [archiveGenerator588] (
  .cons [(.mul archiveGenerator69 archiveGenerator147),
      (.mul archiveGenerator0 archiveGenerator582)] (
  .cons [(.mul archiveGenerator18 archiveGenerator278),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator561))] (
  .cons [archiveGenerator587,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator568)))] (
  .cons [archiveGenerator586,
      (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator133))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator138))))] (
  .cons [archiveGenerator585,
      (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator83)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator188)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator404)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator278))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator147)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator380))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500))))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator146)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator558))))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator137))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator260))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138)))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator137)))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator572),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator138))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator137))))] (
  .cons [] (
  .cons [(.mul archiveGenerator5 archiveGenerator452)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator403))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator402))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator579)] (
  .cons [(.mul archiveGenerator0 archiveGenerator578)] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator553))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator554))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows155 : BasisRows generators 155 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator4 (.mul archiveGenerator7 archiveGenerator324))] (
  .cons [archiveGenerator605] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator446))] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator18 archiveGenerator264)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator584))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator69 archiveGenerator76)),
      (.mul archiveGenerator3 archiveGenerator535),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator524))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator69 archiveGenerator75)),
      (.mul archiveGenerator7 archiveGenerator450),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator523)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator577)))] (
  .cons [(.mul archiveGenerator2 archiveGenerator570),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator521))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator589),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator415)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator4 archiveGenerator486)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator414))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator575)))] (
  .cons [archiveGenerator604,
      (.mul archiveGenerator8 archiveGenerator425),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator562)))))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator67 archiveGenerator75))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator588)] (
  .cons [(.mul archiveGenerator42 archiveGenerator209),
      (.mul archiveGenerator8 archiveGenerator423),
      (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator147)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator582))] (
  .cons [archiveGenerator603,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator261)),
      (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator278))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator209)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator260))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator568))))] (
  .cons [(.mul archiveGenerator13 archiveGenerator346),
      (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator586),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator138)))))] (
  .cons [archiveGenerator602,
      archiveGenerator601,
      archiveGenerator600,
      (.mul archiveGenerator8 archiveGenerator420)] (
  .cons [archiveGenerator599,
      (.mul archiveGenerator17 archiveGenerator292)] (
  .cons [archiveGenerator598,
      (.mul archiveGenerator16 archiveGenerator292),
      (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator219))] (
  .cons [(.mul archiveGenerator64 archiveGenerator149),
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator248)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator260))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator167)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator180))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator259)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator147))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500)))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator258)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator558)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator206))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator257)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138))))))] (
  .cons [archiveGenerator597,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator137))))))] (
  .cons [archiveGenerator596] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator138)))))] (
  .cons [archiveGenerator595] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator403)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator402)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator579))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator578))] (
  .cons [archiveGenerator594] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator554)))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows156 : BasisRows generators 156 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator2 (.mul archiveGenerator13 archiveGenerator324))] (
  .cons [archiveGenerator617,
      (.mul archiveGenerator1 archiveGenerator593)] (
  .cons [(.mul archiveGenerator1 archiveGenerator592),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator446))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator525)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator446)))] (
  .cons [(.mul archiveGenerator15 archiveGenerator324),
      (.mul archiveGenerator13 archiveGenerator368),
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator524)),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator577))] (
  .cons [archiveGenerator616,
      archiveGenerator615,
      (.mul archiveGenerator3 archiveGenerator544),
      (.mul archiveGenerator1 (.mul archiveGenerator14 archiveGenerator324)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator524)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator445),
      (.mul archiveGenerator3 archiveGenerator543),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator544)),
      (.mul archiveGenerator1 archiveGenerator591),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator523)))] (
  .cons [(.mul archiveGenerator8 archiveGenerator443),
      (.mul archiveGenerator7 archiveGenerator459),
      (.mul archiveGenerator2 archiveGenerator575),
      (.mul archiveGenerator1 archiveGenerator590)] (
  .cons [(.mul archiveGenerator3 archiveGenerator540),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator575))] (
  .cons [archiveGenerator614,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator589))] (
  .cons [archiveGenerator613,
      (.mul archiveGenerator9 archiveGenerator408),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator575))))] (
  .cons [archiveGenerator612,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator213)),
      (.mul archiveGenerator0 archiveGenerator604),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator562))))))] (
  .cons [archiveGenerator611,
      archiveGenerator610] (
  .cons [archiveGenerator609,
      (.mul archiveGenerator13 archiveGenerator360)] (
  .cons [archiveGenerator608,
      (.mul archiveGenerator13 archiveGenerator359),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator212)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator69 archiveGenerator147))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator582)))] (
  .cons [(.mul archiveGenerator13 archiveGenerator357),
      (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator188)),
      (.mul archiveGenerator1 archiveGenerator587),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator278)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator267)),
      (.mul archiveGenerator2 (.mul archiveGenerator2 archiveGenerator538)),
      (.mul archiveGenerator1 archiveGenerator586)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator188))),
      (.mul archiveGenerator1 archiveGenerator585),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator586))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator187))),
      (.mul archiveGenerator0 archiveGenerator601),
      (.mul archiveGenerator0 archiveGenerator600)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator24))))),
      (.mul archiveGenerator8 archiveGenerator435),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))),
      (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator292))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23))))),
      (.mul archiveGenerator8 archiveGenerator434),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator101)))),
      (.mul archiveGenerator0 archiveGenerator598),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator292))] (
  .cons [(.mul archiveGenerator16 archiveGenerator299),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator186))),
      (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator149)),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator260)))] (
  .cons [(.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator64)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator20 archiveGenerator80))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator127)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator72))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 (.mul archiveGenerator17 archiveGenerator113))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator32)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator558))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator147))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator13)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator185))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator42)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator184))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator23)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator137)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator17))))))),
      (.mul archiveGenerator0 archiveGenerator596)] (
  .cons [(.mul archiveGenerator17 archiveGenerator298),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator16)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator433),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator125)))),
      (.mul archiveGenerator0 archiveGenerator595)] (
  .cons [(.mul archiveGenerator8 archiveGenerator432),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator50))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator452))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator50)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator71)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator265))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 (.mul archiveGenerator17 archiveGenerator111)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator183)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator182)))] (
  .cons [archiveGenerator607,
      archiveGenerator606] (
  .cons [(.mul archiveGenerator17 archiveGenerator296)] (
  .cons [(.mul archiveGenerator16 archiveGenerator296)] (
  .cons [(.mul archiveGenerator8 archiveGenerator431)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator578)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows157 : BasisRows generators 157 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator4 (.mul archiveGenerator7 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator1 archiveGenerator605),
      (.mul archiveGenerator0 (.mul archiveGenerator2 (.mul archiveGenerator13 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator0 archiveGenerator617)] (
  .cons [(.mul archiveGenerator7 archiveGenerator480)] (
  .cons [(.mul archiveGenerator7 archiveGenerator479),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator446))))] (
  .cons [(.mul archiveGenerator7 archiveGenerator478),
      (.mul archiveGenerator1 (.mul archiveGenerator13 (.mul archiveGenerator69 archiveGenerator76))),
      (.mul archiveGenerator0 (.mul archiveGenerator15 archiveGenerator324))] (
  .cons [(.mul archiveGenerator13 archiveGenerator376),
      (.mul archiveGenerator0 archiveGenerator615),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator544))] (
  .cons [archiveGenerator621,
      (.mul archiveGenerator13 archiveGenerator373),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator445)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator543))] (
  .cons [archiveGenerator620,
      (.mul archiveGenerator8 archiveGenerator450),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator443)),
      (.mul archiveGenerator0 (.mul archiveGenerator2 archiveGenerator575))] (
  .cons [archiveGenerator619,
      (.mul archiveGenerator8 (.mul archiveGenerator18 archiveGenerator209)),
      (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator540))] (
  .cons [archiveGenerator618,
      (.mul archiveGenerator18 archiveGenerator293),
      (.mul archiveGenerator17 archiveGenerator314),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator589)))] (
  .cons [(.mul archiveGenerator16 archiveGenerator314),
      (.mul archiveGenerator1 archiveGenerator604),
      (.mul archiveGenerator0 archiveGenerator613),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator575)))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator449),
      (.mul archiveGenerator0 archiveGenerator612),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator562)))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator448),
      (.mul archiveGenerator0 archiveGenerator610)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator134))),
      (.mul archiveGenerator1 (.mul archiveGenerator42 archiveGenerator209)),
      (.mul archiveGenerator0 archiveGenerator609)] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator133))),
      (.mul archiveGenerator1 archiveGenerator603),
      (.mul archiveGenerator0 archiveGenerator608)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator18 archiveGenerator278))))] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator600),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator188)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator586)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator601)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator600))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator292)))] (
  .cons [(.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator149)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator598)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator292)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator299)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator149))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator260))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator64 archiveGenerator64)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator5 archiveGenerator491),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500)))))))))))))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138))))))))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator137))))))))] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator298))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator433)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator595))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator432))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 archiveGenerator606)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator296))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator296))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator431))] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator594)] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows158 : BasisRows generators 158 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator17 archiveGenerator324),
      (.mul archiveGenerator1 archiveGenerator617)] (
  .cons [archiveGenerator633,
      (.mul archiveGenerator17 (.mul archiveGenerator69 archiveGenerator69)),
      (.mul archiveGenerator16 archiveGenerator324),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator617))] (
  .cons [archiveGenerator632,
      (.mul archiveGenerator16 (.mul archiveGenerator69 archiveGenerator69))] (
  .cons [archiveGenerator631] (
  .cons [(.mul archiveGenerator7 archiveGenerator486),
      (.mul archiveGenerator7 archiveGenerator485),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator15 archiveGenerator324)))] (
  .cons [(.mul archiveGenerator2 archiveGenerator590),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator615)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator544)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator13 archiveGenerator373)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator445))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator543)))] (
  .cons [archiveGenerator630,
      (.mul archiveGenerator1 (.mul archiveGenerator3 archiveGenerator540)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator443)))] (
  .cons [archiveGenerator629,
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator3 archiveGenerator540)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator314))] (
  .cons [archiveGenerator628,
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator613)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator575))))))] (
  .cons [(.mul archiveGenerator9 archiveGenerator423),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator449)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator612)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator562))))))))] (
  .cons [archiveGenerator627,
      (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator261))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator280)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator609))] (
  .cons [archiveGenerator626,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator279)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator608))] (
  .cons [archiveGenerator625,
      (.mul archiveGenerator9 archiveGenerator420),
      (.mul archiveGenerator2 archiveGenerator585),
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator586))] (
  .cons [(.mul archiveGenerator20 archiveGenerator292),
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator220)),
      (.mul archiveGenerator8 archiveGenerator455)] (
  .cons [archiveGenerator624,
      (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator219)),
      (.mul archiveGenerator8 archiveGenerator454),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator586))))] (
  .cons [(.mul archiveGenerator64 archiveGenerator160),
      (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator248)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator278)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator601))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator600)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 archiveGenerator167))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator292))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator194))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator598)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator193))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator299))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator149))))] (
  .cons [archiveGenerator623,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator277))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator149))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324))))))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator149))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500))))))))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator453)] (
  .cons [(.mul archiveGenerator31 archiveGenerator245)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator138)))))))))] (
  .cons [(.mul archiveGenerator8 archiveGenerator452)] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator433))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator595)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator432)))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator1 archiveGenerator606)] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator606))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator296)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator296)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator431)))] (
  .cons [] (
  .cons [] (
  .cons [archiveGenerator622] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private noncomputable def archiveMonomialRows159 : BasisRows generators 159 0 :=
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator324))] (
  .cons [(.mul archiveGenerator18 archiveGenerator314),
      (.mul archiveGenerator0 (.mul archiveGenerator17 (.mul archiveGenerator69 archiveGenerator69))),
      (.mul archiveGenerator0 (.mul archiveGenerator16 archiveGenerator324))] (
  .cons [(.mul archiveGenerator18 archiveGenerator311),
      (.mul archiveGenerator7 (.mul archiveGenerator7 archiveGenerator314)),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator479)),
      (.mul archiveGenerator0 (.mul archiveGenerator16 (.mul archiveGenerator69 archiveGenerator69)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator445),
      (.mul archiveGenerator1 (.mul archiveGenerator7 archiveGenerator478)),
      (.mul archiveGenerator0 archiveGenerator631)] (
  .cons [(.mul archiveGenerator8 archiveGenerator479),
      (.mul archiveGenerator0 (.mul archiveGenerator7 archiveGenerator486))] (
  .cons [(.mul archiveGenerator1 archiveGenerator621)] (
  .cons [(.mul archiveGenerator13 archiveGenerator411)] (
  .cons [(.mul archiveGenerator17 archiveGenerator333),
      (.mul archiveGenerator13 archiveGenerator408),
      (.mul archiveGenerator0 archiveGenerator630)] (
  .cons [(.mul archiveGenerator8 archiveGenerator475),
      (.mul archiveGenerator1 archiveGenerator618),
      (.mul archiveGenerator1 (.mul archiveGenerator18 archiveGenerator293)),
      (.mul archiveGenerator0 archiveGenerator629)] (
  .cons [archiveGenerator640,
      archiveGenerator639,
      (.mul archiveGenerator1 (.mul archiveGenerator1 archiveGenerator604)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator314)))] (
  .cons [archiveGenerator638,
      (.mul archiveGenerator23 archiveGenerator287),
      (.mul archiveGenerator0 archiveGenerator628),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator575)))))))] (
  .cons [(.mul archiveGenerator23 archiveGenerator286),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator449)))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator23 archiveGenerator188)),
      (.mul archiveGenerator0 archiveGenerator627)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator267))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 archiveGenerator188)))] (
  .cons [(.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator23 archiveGenerator101))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator201)))] (
  .cons [(.mul archiveGenerator9 archiveGenerator435),
      (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator80)))),
      (.mul archiveGenerator0 (.mul archiveGenerator20 archiveGenerator292))] (
  .cons [(.mul archiveGenerator8 archiveGenerator471),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator101)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator454)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator586)))))] (
  .cons [(.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator32))))),
      (.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator113)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator23 archiveGenerator80)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator278))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator601)))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator600))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator64 archiveGenerator112)),
      (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator13)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator22 archiveGenerator80)))),
      (.mul archiveGenerator1 (.mul archiveGenerator1 (.mul archiveGenerator64 archiveGenerator149))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator292)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator51))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator80))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator598))))] (
  .cons [archiveGenerator637,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 (.mul archiveGenerator13 archiveGenerator23)))))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator79))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator64 archiveGenerator149)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator154))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator32)))))),
      (.mul archiveGenerator0 archiveGenerator623)] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator154))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator9 (.mul archiveGenerator13 archiveGenerator13))))))),
      (.mul archiveGenerator1 (.mul archiveGenerator5 archiveGenerator491)),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator324)))))))))))))))))))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator138)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator46)))))),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator500)))))))))))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator137)))),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator45))))))] (
  .cons [(.mul archiveGenerator42 archiveGenerator224),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator20)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator225)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator19)))))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator225)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator136)))),
      (.mul archiveGenerator0 (.mul archiveGenerator8 archiveGenerator452))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator16 archiveGenerator224)),
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator56)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator78)))))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator77)))))] (
  .cons [archiveGenerator636,
      (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator283))] (
  .cons [archiveGenerator635,
      (.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator17 archiveGenerator153)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator200)))] (
  .cons [(.mul archiveGenerator8 (.mul archiveGenerator8 (.mul archiveGenerator8 archiveGenerator199)))] (
  .cons [archiveGenerator634] (
  .cons [(.mul archiveGenerator17 archiveGenerator326)] (
  .cons [(.mul archiveGenerator8 archiveGenerator470)] (
  .cons [(.mul archiveGenerator8 archiveGenerator469),
      (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator606)))] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator17 archiveGenerator296))))] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [] (
  .cons [(.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 (.mul archiveGenerator0 archiveGenerator0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))] (
  .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end KIP126.Computation.StandardArchive
