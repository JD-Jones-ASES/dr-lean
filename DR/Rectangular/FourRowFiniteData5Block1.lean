import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 0, row sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block1PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(99/2500), (105461/12500), (-8541103/500000), (65266289/7500000), (20093561/7500000), (-27700469/7500000), (102983/93750), (-12799/125000), 0, 0],
    ![(283/15000), (-64159/600000), (614627/1500000), (2335693/1250000), (-621289/125000), (57696979/15000000), (-2896849/2500000), (35793/312500), 0, 0],
    ![(283/15000), (-64159/600000), (614627/1500000), (2335693/1250000), (-621289/125000), (57696979/15000000), (-2896849/2500000), (35793/312500), 0, 0],
    ![(1451/60000), (2541/10000), (3277781/1500000), (-5232719/750000), (239009/30000), (-5904599/1250000), (2815921/1875000), (-31199/156250), 0, 0]]

private def fourRowFinite5Block1PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block1PowerEntryChunk0]

def fourRowFinite5Block1PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block1PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block1Power : Fin 2 → Fin 2 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block1PowerEntry (2*i.val+j.val)

private def fourRowFinite5Block1BernsteinEntryChunk0 : Array (ℚ) :=
  #[(28179694543/39062500000),
    (21374771719/1562500000000),
    (21374771719/1562500000000),
    (25476245989/390625000000),
    (1172291326811/937500000000),
    (561926373833/37500000000000),
    (561926373833/37500000000000),
    (1090889383883/9375000000000),
    (21850506384757/15000000000000),
    (4835800067689/150000000000000),
    (4835800067689/150000000000000),
    (6724441617379/37500000000000),
    (995382006743/700000000000),
    (4728120770693/70000000000000),
    (4728120770693/70000000000000),
    (760731187513/3500000000000),
    (12949069999709/10500000000000),
    (2231345022451/21000000000000),
    (2231345022451/21000000000000),
    (1176245170501/5250000000000),
    (127095158123/131250000000),
    (55377212209/420000000000),
    (55377212209/420000000000),
    (5386525957/26250000000),
    (48169315557/70000000000),
    (1340014431/10000000000),
    (1340014431/10000000000),
    (592660053/3500000000),
    (650719121/1500000000),
    (333954499/3000000000),
    (333954499/3000000000),
    (372434467/3000000000)]

private def fourRowFinite5Block1BernsteinEntryChunk1 : Array (ℚ) :=
  #[(2137603/9375000),
    (2637307/37500000),
    (2637307/37500000),
    (286201/3750000),
    (6116/78125),
    (1387/62500),
    (1387/62500),
    (19969/625000)]

private def fourRowFinite5Block1BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block1BernsteinEntryChunk0, fourRowFinite5Block1BernsteinEntryChunk1]

def fourRowFinite5Block1BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block1BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block1Bernstein (k : Fin 10) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => fourRowFinite5Block1BernsteinEntry (4*k.val+2*i.val+j.val)

private def fourRowFinite5Block1FactorEntryChunk0 : Array (ℚ) :=
  #[489443240,
    9281273,
    0,
    1,
    4262877552040,
    51084215803,
    0,
    1,
    218505063847570,
    4835800067689,
    0,
    1,
    99538200674300,
    4728120770693,
    0,
    1,
    25898139999418,
    2231345022451,
    0,
    1,
    2033522529968,
    276886061045,
    0,
    1,
    16056438519,
    3126700339,
    0,
    1,
    1301438242,
    333954499,
    0,
    1]

private def fourRowFinite5Block1FactorEntryChunk1 : Array (ℚ) :=
  #[8550412,
    2637307,
    0,
    1,
    24464,
    6935,
    0,
    1]

private def fourRowFinite5Block1FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block1FactorEntryChunk0, fourRowFinite5Block1FactorEntryChunk1]

def fourRowFinite5Block1FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block1FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block1WeightEntryChunk0 : Array (ℚ) :=
  #[(2303/764755062500000000000),
    (49678320427935939153/764755062500000000000),
    (11/159857908201500000000000000),
    (6190868632369355084934127/53285969400500000000000000),
    (1/32775759577135500000000000000),
    (1951304405827986716364625133/10925253192378500000000000000),
    (1/6967674047201000000000000000),
    (1492081146015092158512617751/6967674047201000000000000000),
    (1/543860939987778000000000000),
    (5565302275613329529001251/25898139999418000000000000),
    (1/4270397312932800000000000),
    (53308257369622661590537/284693154195520000000000),
    (1/374650232110000000000),
    (53663809681175828459/374650232110000000000),
    (1/3904314726000000000),
    (124391616863448671/1301438242000000000),
    (1/320640450000000),
    (5838658811957/106880150000000),
    (1/7645000000),
    (196166583/7645000000)]

private def fourRowFinite5Block1WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block1WeightEntryChunk0]

def fourRowFinite5Block1WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block1WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block1Gram (k : Fin 10) : GramCertificate 2 2 where
  weights i := fourRowFinite5Block1WeightEntry (2*k.val+i.val)
  factor i j := fourRowFinite5Block1FactorEntry (4*k.val+2*i.val+j.val)

end
end DittertRybin
