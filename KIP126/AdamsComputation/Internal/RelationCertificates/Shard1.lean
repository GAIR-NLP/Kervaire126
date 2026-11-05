module

import all KIP126.AdamsComputation.Internal.ArchiveData.Relations
import all KIP126.AdamsComputation.Internal.RelationCertificate

/-! Relation certificates for archive chunks 58–113. -/

@[expose] section
namespace KIP126.Computation.CachedStandard
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private theorem coefficientSourceChunk58 :
    (archiveSourceRelationChunks[58].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[58]))

private theorem coefficientSourceChunk59 :
    (archiveSourceRelationChunks[59].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[59]))

private theorem coefficientSourceChunk60 :
    (archiveSourceRelationChunks[60].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[60]))

private theorem coefficientSourceChunk61 :
    (archiveSourceRelationChunks[61].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[61]))

private theorem coefficientSourceChunk62 :
    (archiveSourceRelationChunks[62].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[62]))

private theorem coefficientSourceChunk63 :
    (archiveSourceRelationChunks[63].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[63]))

private theorem coefficientSourceChunk64 :
    (archiveSourceRelationChunks[64].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[64]))

private theorem coefficientSourceChunk65 :
    (archiveSourceRelationChunks[65].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[65]))

private theorem coefficientSourceChunk66 :
    (archiveSourceRelationChunks[66].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[66]))

private theorem coefficientSourceChunk67 :
    (archiveSourceRelationChunks[67].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[67]))

private theorem coefficientSourceChunk68 :
    (archiveSourceRelationChunks[68].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[68]))

private theorem coefficientSourceChunk69 :
    (archiveSourceRelationChunks[69].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[69]))

private theorem coefficientSourceChunk70 :
    (archiveSourceRelationChunks[70].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[70]))

private theorem coefficientSourceChunk71 :
    (archiveSourceRelationChunks[71].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[71]))

private theorem coefficientSourceChunk72 :
    (archiveSourceRelationChunks[72].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[72]))

private theorem coefficientSourceChunk73 :
    (archiveSourceRelationChunks[73].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[73]))

private theorem coefficientSourceChunk74 :
    (archiveSourceRelationChunks[74].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[74]))

private theorem coefficientSourceChunk75 :
    (archiveSourceRelationChunks[75].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[75]))

private theorem coefficientSourceChunk76 :
    (archiveSourceRelationChunks[76].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[76]))

private theorem coefficientSourceChunk77 :
    (archiveSourceRelationChunks[77].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[77]))

private theorem coefficientSourceChunk78 :
    (archiveSourceRelationChunks[78].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[78]))

private theorem coefficientSourceChunk79 :
    (archiveSourceRelationChunks[79].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[79]))

private theorem coefficientSourceChunk80 :
    (archiveSourceRelationChunks[80].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[80]))

private theorem coefficientSourceChunk81 :
    (archiveSourceRelationChunks[81].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[81]))

private theorem coefficientSourceChunk82 :
    (archiveSourceRelationChunks[82].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[82]))

private theorem coefficientSourceChunk83 :
    (archiveSourceRelationChunks[83].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[83]))

private theorem coefficientSourceChunk84 :
    (archiveSourceRelationChunks[84].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[84]))

private theorem coefficientSourceChunk85 :
    (archiveSourceRelationChunks[85].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[85]))

private theorem coefficientSourceChunk86 :
    (archiveSourceRelationChunks[86].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[86]))

private theorem coefficientSourceChunk87 :
    (archiveSourceRelationChunks[87].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[87]))

private theorem coefficientSourceChunk88 :
    (archiveSourceRelationChunks[88].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[88]))

private theorem coefficientSourceChunk89 :
    (archiveSourceRelationChunks[89].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[89]))

private theorem coefficientSourceChunk90 :
    (archiveSourceRelationChunks[90].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[90]))

private theorem coefficientSourceChunk91 :
    (archiveSourceRelationChunks[91].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[91]))

private theorem coefficientSourceChunk92 :
    (archiveSourceRelationChunks[92].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[92]))

private theorem coefficientSourceChunk93 :
    (archiveSourceRelationChunks[93].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[93]))

private theorem coefficientSourceChunk94 :
    (archiveSourceRelationChunks[94].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[94]))

private theorem coefficientSourceChunk95 :
    (archiveSourceRelationChunks[95].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[95]))

private theorem coefficientSourceChunk96 :
    (archiveSourceRelationChunks[96].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[96]))

private theorem coefficientSourceChunk97 :
    (archiveSourceRelationChunks[97].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[97]))

private theorem coefficientSourceChunk98 :
    (archiveSourceRelationChunks[98].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[98]))

private theorem coefficientSourceChunk99 :
    (archiveSourceRelationChunks[99].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[99]))

private theorem coefficientSourceChunk100 :
    (archiveSourceRelationChunks[100].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[100]))

private theorem coefficientSourceChunk101 :
    (archiveSourceRelationChunks[101].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[101]))

private theorem coefficientSourceChunk102 :
    (archiveSourceRelationChunks[102].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[102]))

private theorem coefficientSourceChunk103 :
    (archiveSourceRelationChunks[103].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[103]))

private theorem coefficientSourceChunk104 :
    (archiveSourceRelationChunks[104].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[104]))

private theorem coefficientSourceChunk105 :
    (archiveSourceRelationChunks[105].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[105]))

private theorem coefficientSourceChunk106 :
    (archiveSourceRelationChunks[106].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[106]))

private theorem coefficientSourceChunk107 :
    (archiveSourceRelationChunks[107].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[107]))

private theorem coefficientSourceChunk108 :
    (archiveSourceRelationChunks[108].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[108]))

private theorem coefficientSourceChunk109 :
    (archiveSourceRelationChunks[109].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[109]))

private theorem coefficientSourceChunk110 :
    (archiveSourceRelationChunks[110].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[110]))

private theorem coefficientSourceChunk111 :
    (archiveSourceRelationChunks[111].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[111]))

private theorem coefficientSourceChunk112 :
    (archiveSourceRelationChunks[112].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[112]))

private theorem coefficientSourceChunk113 :
    (archiveSourceRelationChunks[113].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[113]))

end KIP126.Computation.CachedStandard
