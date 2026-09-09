import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 2, row sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block9PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(51341/60000), (532243/37500), (-25272307/750000), (2244189/78125), (-34023991/2500000), (8938843/1875000), (-279641/250000), (66123/625000), 0, 0],
    ![(1417/30000), (-339943/600000), (871501/375000), (10556547/2500000), (-69835681/5000000), (166843843/15000000), (-16869511/5000000), (835341/2500000), 0, 0],
    ![(1417/30000), (-339943/600000), (871501/375000), (10556547/2500000), (-69835681/5000000), (166843843/15000000), (-16869511/5000000), (835341/2500000), 0, 0],
    ![(969/10000), (-5639/10000), (1451019/250000), (-252499/25000), (18121367/2500000), (-8384111/2500000), (777813/625000), (-27981/125000), 0, 0]]

private def fourRowFinite5Block9PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block9PowerEntryChunk0]

def fourRowFinite5Block9PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block9PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block9Power : Fin 2 → Fin 2 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block9PowerEntry (2*i.val+j.val)

private def fourRowFinite5Block9BernsteinEntryChunk0 : Array (ℚ) :=
  #[(1535504009431/781250000000),
    (52343710167/3125000000000),
    (52343710167/3125000000000),
    (1392864693/15625000000),
    (52346181804977/18750000000000),
    (354750311643/25000000000000),
    (354750311643/25000000000000),
    (75796266977/625000000000),
    (56935101895639/18750000000000),
    (949468849353/12500000000000),
    (949468849353/12500000000000),
    (1124468031923/5000000000000),
    (101698499455139/35000000000000),
    (27900670186821/140000000000000),
    (27900670186821/140000000000000),
    (1464795466509/4375000000000),
    (13365891406691/5250000000000),
    (2345581760793/7000000000000),
    (2345581760793/7000000000000),
    (1455218495659/3500000000000),
    (2167051036193/1050000000000),
    (301597959141/700000000000),
    (301597959141/700000000000),
    (5625641921/12500000000),
    (26931785127/17500000000),
    (3176952909/7000000000),
    (3176952909/7000000000),
    (15114547233/35000000000),
    (12368723/12000000),
    (797444607/2000000000),
    (797444607/2000000000),
    (182834539/500000000)]

private def fourRowFinite5Block9BernsteinEntryChunk1 : Array (ℚ) :=
  #[(10923157/18750000),
    (7105347/25000000),
    (7105347/25000000),
    (1328153/5000000),
    (34853/156250),
    (17913/125000),
    (17913/125000),
    (190839/1250000)]

private def fourRowFinite5Block9BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block9BernsteinEntryChunk0, fourRowFinite5Block9BernsteinEntryChunk1]

def fourRowFinite5Block9BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block9BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block9Bernstein (k : Fin 10) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => fourRowFinite5Block9BernsteinEntry (4*k.val+2*i.val+j.val)

private def fourRowFinite5Block9FactorEntryChunk0 : Array (ℚ) :=
  #[2666963108,
    22728489,
    0,
    1,
    209384727219908,
    1064250934929,
    0,
    1,
    113870203791278,
    2848406548059,
    0,
    1,
    406793997820556,
    27900670186821,
    0,
    1,
    53463565626764,
    7036745282379,
    0,
    1,
    4334102072386,
    904793877423,
    0,
    1,
    1381117186,
    407301655,
    0,
    1,
    6184361500,
    2392333821,
    0,
    1]

private def fourRowFinite5Block9FactorEntryChunk1 : Array (ℚ) :=
  #[43692628,
    21316041,
    0,
    1,
    19916,
    12795,
    0,
    1]

private def fourRowFinite5Block9FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block9FactorEntryChunk0, fourRowFinite5Block9FactorEntryChunk1]

def fourRowFinite5Block9FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block9FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block9WeightEntryChunk0 : Array (ℚ) :=
  #[(2303/8334259712500000000000),
    (741754056692599321137/8334259712500000000000),
    (1/15703854541493100000000000000),
    (634445684059826213431046293/5234618180497700000000000000),
    (1/4270132642172925000000000000),
    (158702018295974067453431579/711688773695487500000000000),
    (1/56951159694877840000000000000),
    (18289392725066156394230202087/56951159694877840000000000000),
    (1/1122734878162044000000000000),
    (27819415539639417656093681/74848991877469600000000000),
    (1/9101614352010600000000000),
    (1092513966391179936862693/3033871450670200000000000),
    (39/48339101510000000000),
    (2057867150520174909/6905585930000000000),
    (1/37106169000000000000),
    (2615105831747240653/12368723000000000000),
    (1/3276947100000000),
    (138694606809193/1092315700000000),
    (7/12447500000),
    (754390587/12447500000)]

private def fourRowFinite5Block9WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block9WeightEntryChunk0]

def fourRowFinite5Block9WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block9WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block9Gram (k : Fin 10) : GramCertificate 2 2 where
  weights i := fourRowFinite5Block9WeightEntry (2*k.val+i.val)
  factor i j := fourRowFinite5Block9FactorEntry (4*k.val+2*i.val+j.val)

end
end DittertRybin
