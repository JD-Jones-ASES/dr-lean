import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=50, triple seed 4, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite50Block19PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(410709/100000000), (645263173/2500000000), (2136318539199/250000000000), (-73258280678827/6250000000000), (17605280324607/3125000000000), (-1765607986929/3125000000000), (974473227/50000000000), (-1293830847/6250000000000), 0, 0]]

private def fourRowFinite50Block19PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite50Block19PowerEntryChunk0]

def fourRowFinite50Block19PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite50Block19PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite50Block19Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite50Block19PowerEntry (1*i.val+j.val)

private def fourRowFinite50Block19BernsteinEntryChunk0 : Array (ℚ) :=
  #[(6512923254558761103/62500000000000000000),
    (8374504698395632337/31250000000000000000),
    (138097567033905143147/250000000000000000000),
    (10934634541784633283/12500000000000000000),
    (2065614043907621479/1750000000000000000),
    (157460873352560747/109375000000000000),
    (160739467972929/97656250000000),
    (1133207588665411/625000000000000),
    (7707593547029/3906250000000),
    (106159140969/48828125000)]

private def fourRowFinite50Block19BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block19BernsteinEntryChunk0]

def fourRowFinite50Block19BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block19BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block19Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite50Block19BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite50Block19FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite50Block19FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block19FactorEntryChunk0]

def fourRowFinite50Block19FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block19FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite50Block19WeightEntryChunk0 : Array (ℚ) :=
  #[(6512923254558761103/62500000000000000000),
    (8374504698395632337/31250000000000000000),
    (138097567033905143147/250000000000000000000),
    (10934634541784633283/12500000000000000000),
    (2065614043907621479/1750000000000000000),
    (157460873352560747/109375000000000000),
    (160739467972929/97656250000000),
    (1133207588665411/625000000000000),
    (7707593547029/3906250000000),
    (106159140969/48828125000)]

private def fourRowFinite50Block19WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block19WeightEntryChunk0]

def fourRowFinite50Block19WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block19WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block19Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite50Block19WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite50Block19FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
