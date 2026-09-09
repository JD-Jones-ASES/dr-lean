import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 5, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block23PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(5177/2500), (-363063/50000), (354791/31250), (-11306863/1250000), (4023233/1250000), (-41969/312500), (-210917/1250000), (3081/125000), 0, 0]]

private def fourRowFinite5Block23PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block23PowerEntryChunk0]

def fourRowFinite5Block23PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block23PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block23Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block23PowerEntry (1*i.val+j.val)

private def fourRowFinite5Block23BernsteinEntryChunk0 : Array (ℚ) :=
  #[(226481559213/156250000000),
    (1155706840169/1250000000000),
    (59835072077/100000000000),
    (14117732669451/35000000000000),
    (126180872887/437500000000),
    (9516125963/43750000000),
    (5874219243/35000000000),
    (1985263/15625000),
    (282421/3125000),
    (4497/78125)]

private def fourRowFinite5Block23BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block23BernsteinEntryChunk0]

def fourRowFinite5Block23BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block23BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block23Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite5Block23BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite5Block23FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite5Block23FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block23FactorEntryChunk0]

def fourRowFinite5Block23FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block23FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block23WeightEntryChunk0 : Array (ℚ) :=
  #[(226481559213/156250000000),
    (1155706840169/1250000000000),
    (59835072077/100000000000),
    (14117732669451/35000000000000),
    (126180872887/437500000000),
    (9516125963/43750000000),
    (5874219243/35000000000),
    (1985263/15625000),
    (282421/3125000),
    (4497/78125)]

private def fourRowFinite5Block23WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block23WeightEntryChunk0]

def fourRowFinite5Block23WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block23WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block23Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite5Block23WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite5Block23FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
