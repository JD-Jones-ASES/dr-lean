import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 4, column sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block18PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(-39/400), (196371/5000), (-4715137/50000), (12419461/125000), (-69460067/1250000), (10212271/625000), (-2851209/1250000), (14481/125000), 0, 0],
    ![(-63/1000), (711957/20000), (-9463677/100000), (13291023/125000), (-27521781/500000), (26845287/2500000), (233487/1250000), (-13176/78125), 0, 0],
    ![(-63/1000), (711957/20000), (-9463677/100000), (13291023/125000), (-27521781/500000), (26845287/2500000), (233487/1250000), (-13176/78125), 0, 0],
    ![(61/1200), (328773/10000), (-4669683/50000), (14131449/125000), (-234265829/3750000), (16634359/1250000), (-112161/1250000), (-20961/125000), 0, 0]]

private def fourRowFinite5Block18PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block18PowerEntryChunk0]

def fourRowFinite5Block18PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block18PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block18Power : Fin 2 → Fin 2 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block18PowerEntry (2*i.val+j.val)

private def fourRowFinite5Block18BernsteinEntryChunk0 : Array (ℚ) :=
  #[(465758220249/156250000000),
    (2071366155369/781250000000),
    (2071366155369/781250000000),
    (392431907021/156250000000),
    (1324715257281/250000000000),
    (28849395715581/6250000000000),
    (28849395715581/6250000000000),
    (636937821667/150000000000),
    (15235729506483/2500000000000),
    (127423966037703/25000000000000),
    (127423966037703/25000000000000),
    (8552504335249/1875000000000),
    (211760426923407/35000000000000),
    (4835558053971/1000000000000),
    (4835558053971/1000000000000),
    (148141214538083/35000000000000),
    (4901279656461/875000000000),
    (15099692521101/3500000000000),
    (15099692521101/3500000000000),
    (19661809280261/5250000000000),
    (437856429081/87500000000),
    (33315712077/8750000000),
    (33315712077/8750000000),
    (1761416234629/525000000000),
    (1372650237/312500000),
    (3004206867/875000000),
    (3004206867/875000000),
    (55135492323/17500000000),
    (955768521/250000000),
    (3202255497/1000000000),
    (3202255497/1000000000),
    (2331511037/750000000)]

private def fourRowFinite5Block18BernsteinEntryChunk1 : Array (ℚ) :=
  #[(10335693/3125000),
    (1531209/500000),
    (1531209/500000),
    (29499401/9375000),
    (221571/78125),
    (918423/312500),
    (918423/312500),
    (49457/15625)]

private def fourRowFinite5Block18BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block18BernsteinEntryChunk0, fourRowFinite5Block18BernsteinEntryChunk1]

def fourRowFinite5Block18BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block18BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block18Bernstein (k : Fin 10) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => fourRowFinite5Block18BernsteinEntry (4*k.val+2*i.val+j.val)

private def fourRowFinite5Block18FactorEntryChunk0 : Array (ℚ) :=
  #[112355435,
    99935647,
    0,
    1,
    11039293810675,
    9616465238527,
    0,
    1,
    50785765021610,
    42474655345901,
    0,
    1,
    23528936324823,
    18804947987665,
    0,
    1,
    6535039541948,
    5033230840367,
    0,
    1,
    145952143027,
    111052373590,
    0,
    1,
    2135233702,
    1669003815,
    0,
    1,
    1274358028,
    1067418499,
    0,
    1]

private def fourRowFinite5Block18FactorEntryChunk1 : Array (ℚ) :=
  #[13780924,
    12760075,
    0,
    1,
    98476,
    102047,
    0,
    1]

private def fourRowFinite5Block18FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block18FactorEntryChunk0, fourRowFinite5Block18FactorEntryChunk1]

def fourRowFinite5Block18FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block18FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block18WeightEntryChunk0 : Array (ℚ) :=
  #[(20727/87777683593750000000),
    (3363992798854126733/21944420898437500000),
    (3/68995586316718750000000000),
    (11657583977495723078933891/51746689737539062500000000),
    (3/1269644125540250000000000000),
    (1136951899872574385171719391/3808932376620750000000000000),
    (3/274504257122935000000000000),
    (25247548714952066888530357/68626064280733750000000000),
    (3/22872638396818000000000000),
    (5796137598739617733104931/13723583038090800000000000),
    (3/12770812514862500000000),
    (35095139967138867496183/76624875089175000000000),
    (9/9341647446250000000),
    (8723253471493958823/18683294892500000000),
    (3/1274358028000000000),
    (326055792283900627/764614816800000000),
    (3/172261550000000),
    (160740386855471/516784650000000),
    (9/30773750000),
    (3684238759/30773750000)]

private def fourRowFinite5Block18WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block18WeightEntryChunk0]

def fourRowFinite5Block18WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block18WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block18Gram (k : Fin 10) : GramCertificate 2 2 where
  weights i := fourRowFinite5Block18WeightEntry (2*k.val+i.val)
  factor i j := fourRowFinite5Block18FactorEntry (4*k.val+2*i.val+j.val)

end
end DittertRybin
