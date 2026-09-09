import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 1, column sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block6PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(987/20000), (1566253/100000), (-7986751/375000), (-14033783/3750000), (6287953/375000), (-64521563/7500000), (4140061/2500000), (-136791/1250000), 0, 0],
    ![(2561/24000), (392571/40000), (-180877/25000), (-2433223/125000), (107164789/3750000), (-71886157/5000000), (15603661/5000000), (-612111/2500000), 0, 0],
    ![(2561/24000), (392571/40000), (-180877/25000), (-2433223/125000), (107164789/3750000), (-71886157/5000000), (15603661/5000000), (-612111/2500000), 0, 0],
    ![(8141/22500), (235153/37500), (3691/93750), (-589178953/22500000), (738341477/22500000), (-367934981/22500000), (81772331/22500000), (-220351/750000), 0, 0]]

private def fourRowFinite5Block6PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block6PowerEntryChunk0]

def fourRowFinite5Block6PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block6PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block6Power : Fin 2 → Fin 2 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block6PowerEntry (2*i.val+j.val)

private def fourRowFinite5Block6BernsteinEntryChunk0 : Array (ℚ) :=
  #[(2188239117183/1562500000000),
    (3121988440543/3125000000000),
    (3121988440543/3125000000000),
    (905837306507/937500000000),
    (31697822761507/12500000000000),
    (134107158842441/75000000000000),
    (134107158842441/75000000000000),
    (34376881145533/22500000000000),
    (9960840922211/3125000000000),
    (86940745285811/37500000000000),
    (86940745285811/37500000000000),
    (4397334460679/2250000000000),
    (236176584081729/70000000000000),
    (351166927890689/140000000000000),
    (351166927890689/140000000000000),
    (444957625979429/210000000000000),
    (11130029858497/3500000000000),
    (50188609006799/21000000000000),
    (50188609006799/21000000000000),
    (2552079981431/1260000000000),
    (47613957493/17500000000),
    (134546398097/65625000000),
    (134546398097/65625000000),
    (5489712417823/3150000000000),
    (9258022551/4375000000),
    (111368624163/70000000000),
    (111368624163/70000000000),
    (3804298779/2800000000),
    (1473182993/1000000000),
    (1324676669/1200000000),
    (1324676669/1200000000),
    (2144817103/2250000000)]

private def fourRowFinite5Block6BernsteinEntryChunk1 : Array (ℚ) :=
  #[(10955657/12500000),
    (9870497/15000000),
    (9870497/15000000),
    (6585097/11250000),
    (119727/312500),
    (185033/625000),
    (185033/625000),
    (135583/468750)]

private def fourRowFinite5Block6BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block6BernsteinEntryChunk0, fourRowFinite5Block6BernsteinEntryChunk1]

def fourRowFinite5Block6BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block6BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block6Bernstein (k : Fin 10) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => fourRowFinite5Block6BernsteinEntry (4*k.val+2*i.val+j.val)

private def fourRowFinite5Block6FactorEntryChunk0 : Array (ℚ) :=
  #[1900337922,
    1355618081,
    0,
    1,
    190186936569042,
    134107158842441,
    0,
    1,
    119530091066532,
    86940745285811,
    0,
    1,
    472353168163458,
    351166927890689,
    0,
    1,
    66780179150982,
    50188609006799,
    0,
    1,
    714209362395,
    538185592388,
    0,
    1,
    49376120272,
    37122874721,
    0,
    1,
    8839097958,
    6623383345,
    0,
    1]

private def fourRowFinite5Block6FactorEntryChunk1 : Array (ℚ) :=
  #[65733942,
    49352485,
    0,
    1,
    239454,
    185033,
    0,
    1]

private def fourRowFinite5Block6FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block6FactorEntryChunk0, fourRowFinite5Block6FactorEntryChunk1]

def fourRowFinite5Block6FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block6FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block6WeightEntryChunk0 : Array (ℚ) :=
  #[(329/848365143750000000000),
    (215109424340792467171/848365143750000000000),
    (1/14264020242678150000000000000),
    (3808715660098233897285126139/14264020242678150000000000000),
    (1/4482378414994950000000000000),
    (1201536618063736515370326079/4482378414994950000000000000),
    (1/66129443542884120000000000000),
    (5599961658577271731181814089/22043147847628040000000000000),
    (1/1402383762170622000000000000),
    (321576165422604226528694299/1402383762170622000000000000),
    (1/187479957628687500000000),
    (148359741139002953818519/749919830514750000000000),
    (3/3456328419040000000000),
    (80244909844283744811/493761202720000000000),
    (1/53034587748000000000),
    (6686122332938679439/53034587748000000000),
    (1/4930045650000000),
    (90018957214787/986009130000000),
    (1/149658750000),
    (9050644487/149658750000)]

private def fourRowFinite5Block6WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block6WeightEntryChunk0]

def fourRowFinite5Block6WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block6WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block6Gram (k : Fin 10) : GramCertificate 2 2 where
  weights i := fourRowFinite5Block6WeightEntry (2*k.val+i.val)
  factor i j := fourRowFinite5Block6FactorEntry (4*k.val+2*i.val+j.val)

end
end DittertRybin
