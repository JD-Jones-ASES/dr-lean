import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 1, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block7PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(40087/60000), (-36529/100000), (-1140351/500000), (34033163/7500000), (-14602601/3750000), (1637417/937500), (-3629/9375), (503/15625), 0, 0]]

private def fourRowFinite5Block7PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block7PowerEntryChunk0]

def fourRowFinite5Block7PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block7PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block7Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block7PowerEntry (1*i.val+j.val)

private def fourRowFinite5Block7BernsteinEntryChunk0 : Array (ℚ) :=
  #[(23943206287/39062500000),
    (509009741489/937500000000),
    (1677669565087/3750000000000),
    (309368084521/875000000000),
    (179015627729/656250000000),
    (108903244481/525000000000),
    (2181547089/14000000000),
    (86353357/750000000),
    (1554671/18750000),
    (8989/156250)]

private def fourRowFinite5Block7BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block7BernsteinEntryChunk0]

def fourRowFinite5Block7BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block7BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block7Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite5Block7BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite5Block7FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite5Block7FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block7FactorEntryChunk0]

def fourRowFinite5Block7FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block7FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block7WeightEntryChunk0 : Array (ℚ) :=
  #[(23943206287/39062500000),
    (509009741489/937500000000),
    (1677669565087/3750000000000),
    (309368084521/875000000000),
    (179015627729/656250000000),
    (108903244481/525000000000),
    (2181547089/14000000000),
    (86353357/750000000),
    (1554671/18750000),
    (8989/156250)]

private def fourRowFinite5Block7WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block7WeightEntryChunk0]

def fourRowFinite5Block7WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block7WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block7Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite5Block7WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite5Block7FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
