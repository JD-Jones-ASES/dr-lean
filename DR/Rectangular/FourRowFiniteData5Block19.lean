import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 4, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block19PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(-157/5000), (166689/50000), (-1210017/125000), (17290989/1250000), (-15038141/1250000), (74721/12500), (-1831023/1250000), (81783/625000), 0, 0]]

private def fourRowFinite5Block19PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block19PowerEntryChunk0]

def fourRowFinite5Block19PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block19PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block19Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block19PowerEntry (1*i.val+j.val)

private def fourRowFinite5Block19BernsteinEntryChunk0 : Array (ℚ) :=
  #[(170206800771/781250000000),
    (2466352125959/6250000000000),
    (5399890278731/12500000000000),
    (14462442692673/35000000000000),
    (163319779643/437500000000),
    (14135817499/43750000000),
    (1852347951/7000000000),
    (24924967/125000000),
    (411587/3125000),
    (5331/78125)]

private def fourRowFinite5Block19BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block19BernsteinEntryChunk0]

def fourRowFinite5Block19BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block19BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block19Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite5Block19BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite5Block19FactorEntryChunk0 : Array (ℚ) :=
  #[1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1]

private def fourRowFinite5Block19FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block19FactorEntryChunk0]

def fourRowFinite5Block19FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block19FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block19WeightEntryChunk0 : Array (ℚ) :=
  #[(170206800771/781250000000),
    (2466352125959/6250000000000),
    (5399890278731/12500000000000),
    (14462442692673/35000000000000),
    (163319779643/437500000000),
    (14135817499/43750000000),
    (1852347951/7000000000),
    (24924967/125000000),
    (411587/3125000),
    (5331/78125)]

private def fourRowFinite5Block19WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block19WeightEntryChunk0]

def fourRowFinite5Block19WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block19WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block19Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite5Block19WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite5Block19FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
