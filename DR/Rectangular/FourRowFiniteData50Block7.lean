import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=50, triple seed 1, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite50Block7PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(-185499059/300000000), (102501268729/15000000000), (6563743737617/250000000000), (-1738144823330021/37500000000000), (4180128908069/187500000000), (-83662799359937/37500000000000), (240211521197/3125000000000), (-159369351/195312500000), 0, 0]]

private def fourRowFinite50Block7PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite50Block7PowerEntryChunk0]

def fourRowFinite50Block7PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite50Block7PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite50Block7Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite50Block7PowerEntry (1*i.val+j.val)

private def fourRowFinite50Block7BernsteinEntryChunk0 : Array (ℚ) :=
  #[(8856812016659685379/31250000000000000000),
    (31912832994743980009/23437500000000000000),
    (1006083559927516607/366210937500000000),
    (71988432822157663639/17500000000000000000),
    (55064143939224516967/10500000000000000000),
    (6323802271776529691/1050000000000000000),
    (2248054275642093861/350000000000000000),
    (19500852739955909/3000000000000000),
    (598290623409287/93750000000000),
    (2444765087009/390625000000)]

private def fourRowFinite50Block7BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block7BernsteinEntryChunk0]

def fourRowFinite50Block7BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block7BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block7Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite50Block7BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite50Block7FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite50Block7FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block7FactorEntryChunk0]

def fourRowFinite50Block7FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block7FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite50Block7WeightEntryChunk0 : Array (ℚ) :=
  #[(8856812016659685379/31250000000000000000),
    (31912832994743980009/23437500000000000000),
    (1006083559927516607/366210937500000000),
    (71988432822157663639/17500000000000000000),
    (55064143939224516967/10500000000000000000),
    (6323802271776529691/1050000000000000000),
    (2248054275642093861/350000000000000000),
    (19500852739955909/3000000000000000),
    (598290623409287/93750000000000),
    (2444765087009/390625000000)]

private def fourRowFinite50Block7WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block7WeightEntryChunk0]

def fourRowFinite50Block7WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block7WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block7Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite50Block7WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite50Block7FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
