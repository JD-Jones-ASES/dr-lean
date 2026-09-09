import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=50, triple seed 6, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite50Block27PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(12029/7500000), (13768501367/750000000), (-901345673201/18750000000), (102113034054017/1875000000000), (-120234578120177/4687500000000), (24066842804191/9375000000000), (-829764110687/9375000000000), (2937346351/3125000000000), 0, 0]]

private def fourRowFinite50Block27PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite50Block27PowerEntryChunk0]

def fourRowFinite50Block27PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite50Block27PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite50Block27Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite50Block27PowerEntry (1*i.val+j.val)

private def fourRowFinite50Block27BernsteinEntryChunk0 : Array (ℚ) :=
  #[(44018975623120615761/31250000000000000000),
    (38065948136190451489/15625000000000000000),
    (339471664908117262969/125000000000000000000),
    (57598469300135378109/21875000000000000000),
    (191170189276584011/78125000000000000),
    (1006767572743596113/437500000000000000),
    (12225066440691141/5468750000000000),
    (2745312644731967/1250000000000000),
    (63968973875779/31250000000000),
    (616265479137/390625000000)]

private def fourRowFinite50Block27BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block27BernsteinEntryChunk0]

def fourRowFinite50Block27BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block27BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block27Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite50Block27BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite50Block27FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite50Block27FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block27FactorEntryChunk0]

def fourRowFinite50Block27FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block27FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite50Block27WeightEntryChunk0 : Array (ℚ) :=
  #[(44018975623120615761/31250000000000000000),
    (38065948136190451489/15625000000000000000),
    (339471664908117262969/125000000000000000000),
    (57598469300135378109/21875000000000000000),
    (191170189276584011/78125000000000000),
    (1006767572743596113/437500000000000000),
    (12225066440691141/5468750000000000),
    (2745312644731967/1250000000000000),
    (63968973875779/31250000000000),
    (616265479137/390625000000)]

private def fourRowFinite50Block27WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block27WeightEntryChunk0]

def fourRowFinite50Block27WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block27WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block27Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite50Block27WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite50Block27FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
