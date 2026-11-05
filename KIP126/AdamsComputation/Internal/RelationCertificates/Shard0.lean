module

import all KIP126.AdamsComputation.Internal.ArchiveData.Relations
import all KIP126.AdamsComputation.Internal.RelationCertificate

/-! Relation certificates for archive chunks 0–57. -/

@[expose] section
namespace KIP126.Computation.CachedStandard
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private theorem coefficientSourceChunk0 :
    (archiveSourceRelationChunks[0].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[0]))

private theorem coefficientSourceChunk1 :
    (archiveSourceRelationChunks[1].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[1]))

private theorem coefficientSourceChunk2 :
    (archiveSourceRelationChunks[2].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[2]))

private theorem coefficientSourceChunk3 :
    (archiveSourceRelationChunks[3].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[3]))

private theorem coefficientSourceChunk4 :
    (archiveSourceRelationChunks[4].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[4]))

private theorem coefficientSourceChunk5 :
    (archiveSourceRelationChunks[5].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[5]))

private theorem coefficientSourceChunk6 :
    (archiveSourceRelationChunks[6].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[6]))

private theorem coefficientSourceChunk7 :
    (archiveSourceRelationChunks[7].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[7]))

private theorem coefficientSourceChunk8 :
    (archiveSourceRelationChunks[8].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[8]))

private theorem coefficientSourceChunk9 :
    (archiveSourceRelationChunks[9].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[9]))

private theorem coefficientSourceChunk10 :
    (archiveSourceRelationChunks[10].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[10]))

private theorem coefficientSourceChunk11 :
    (archiveSourceRelationChunks[11].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[11]))

private theorem coefficientSourceChunk12 :
    (archiveSourceRelationChunks[12].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[12]))

private theorem coefficientSourceChunk13 :
    (archiveSourceRelationChunks[13].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[13]))

private theorem coefficientSourceChunk14 :
    (archiveSourceRelationChunks[14].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[14]))

private theorem coefficientSourceChunk15 :
    (archiveSourceRelationChunks[15].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[15]))

private theorem coefficientSourceChunk16 :
    (archiveSourceRelationChunks[16].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[16]))

private theorem coefficientSourceChunk17 :
    (archiveSourceRelationChunks[17].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[17]))

private theorem coefficientSourceChunk18 :
    (archiveSourceRelationChunks[18].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[18]))

private theorem coefficientSourceChunk19 :
    (archiveSourceRelationChunks[19].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[19]))

private theorem coefficientSourceChunk20 :
    (archiveSourceRelationChunks[20].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[20]))

private theorem coefficientSourceChunk21 :
    (archiveSourceRelationChunks[21].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[21]))

private theorem coefficientSourceChunk22 :
    (archiveSourceRelationChunks[22].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[22]))

private theorem coefficientSourceChunk23 :
    (archiveSourceRelationChunks[23].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[23]))

private theorem coefficientSourceChunk24 :
    (archiveSourceRelationChunks[24].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[24]))

private theorem coefficientSourceChunk25 :
    (archiveSourceRelationChunks[25].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[25]))

private theorem coefficientSourceChunk26 :
    (archiveSourceRelationChunks[26].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[26]))

private theorem coefficientSourceChunk27 :
    (archiveSourceRelationChunks[27].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[27]))

private theorem coefficientSourceChunk28 :
    (archiveSourceRelationChunks[28].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[28]))

private theorem coefficientSourceChunk29 :
    (archiveSourceRelationChunks[29].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[29]))

private theorem coefficientSourceChunk30 :
    (archiveSourceRelationChunks[30].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[30]))

private theorem coefficientSourceChunk31 :
    (archiveSourceRelationChunks[31].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[31]))

private theorem coefficientSourceChunk32 :
    (archiveSourceRelationChunks[32].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[32]))

private theorem coefficientSourceChunk33 :
    (archiveSourceRelationChunks[33].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[33]))

private theorem coefficientSourceChunk34 :
    (archiveSourceRelationChunks[34].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[34]))

private theorem coefficientSourceChunk35 :
    (archiveSourceRelationChunks[35].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[35]))

private theorem coefficientSourceChunk36 :
    (archiveSourceRelationChunks[36].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[36]))

private theorem coefficientSourceChunk37 :
    (archiveSourceRelationChunks[37].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[37]))

private theorem coefficientSourceChunk38 :
    (archiveSourceRelationChunks[38].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[38]))

private theorem coefficientSourceChunk39 :
    (archiveSourceRelationChunks[39].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[39]))

private theorem coefficientSourceChunk40 :
    (archiveSourceRelationChunks[40].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[40]))

private theorem coefficientSourceChunk41 :
    (archiveSourceRelationChunks[41].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[41]))

private theorem coefficientSourceChunk42 :
    (archiveSourceRelationChunks[42].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[42]))

private theorem coefficientSourceChunk43 :
    (archiveSourceRelationChunks[43].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[43]))

private theorem coefficientSourceChunk44 :
    (archiveSourceRelationChunks[44].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[44]))

private theorem coefficientSourceChunk45 :
    (archiveSourceRelationChunks[45].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[45]))

private theorem coefficientSourceChunk46 :
    (archiveSourceRelationChunks[46].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[46]))

private theorem coefficientSourceChunk47 :
    (archiveSourceRelationChunks[47].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[47]))

private theorem coefficientSourceChunk48 :
    (archiveSourceRelationChunks[48].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[48]))

private theorem coefficientSourceChunk49 :
    (archiveSourceRelationChunks[49].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[49]))

private theorem coefficientSourceChunk50 :
    (archiveSourceRelationChunks[50].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[50]))

private theorem coefficientSourceChunk51 :
    (archiveSourceRelationChunks[51].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[51]))

private theorem coefficientSourceChunk52 :
    (archiveSourceRelationChunks[52].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[52]))

private theorem coefficientSourceChunk53 :
    (archiveSourceRelationChunks[53].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[53]))

private theorem coefficientSourceChunk54 :
    (archiveSourceRelationChunks[54].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[54]))

private theorem coefficientSourceChunk55 :
    (archiveSourceRelationChunks[55].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[55]))

private theorem coefficientSourceChunk56 :
    (archiveSourceRelationChunks[56].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[56]))

private theorem coefficientSourceChunk57 :
    (archiveSourceRelationChunks[57].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[57]))

end KIP126.Computation.CachedStandard
