import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=50, triple seed 2, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite50Block11PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(-145207881/100000000), (16647955367/625000000), (1662342663159/250000000000), (-28277961167883/1562500000000), (84926660796247/12500000000000), (-8004785940277/12500000000000), (269160110903/12500000000000), (-2824792599/12500000000000), 0, 0]]

private def fourRowFinite50Block11PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite50Block11PowerEntryChunk0]

def fourRowFinite50Block11PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite50Block11PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite50Block11Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite50Block11PowerEntry (1*i.val+j.val)

private def fourRowFinite50Block11BernsteinEntryChunk0 : Array (ℚ) :=
  #[(157582861383342895731/125000000000000000000),
    (250357202527344465609/62500000000000000000),
    (3393623178065466349659/500000000000000000000),
    (331492898768778722853/35000000000000000000),
    (104626813949527540059/8750000000000000000),
    (12404090565639584739/875000000000000000),
    (5630082695555933133/350000000000000000),
    (22088330061790761/1250000000000000),
    (147943597238379/7812500000000),
    (388890275319/19531250000)]

private def fourRowFinite50Block11BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block11BernsteinEntryChunk0]

def fourRowFinite50Block11BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block11BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block11Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite50Block11BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite50Block11FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite50Block11FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block11FactorEntryChunk0]

def fourRowFinite50Block11FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block11FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite50Block11WeightEntryChunk0 : Array (ℚ) :=
  #[(157582861383342895731/125000000000000000000),
    (250357202527344465609/62500000000000000000),
    (3393623178065466349659/500000000000000000000),
    (331492898768778722853/35000000000000000000),
    (104626813949527540059/8750000000000000000),
    (12404090565639584739/875000000000000000),
    (5630082695555933133/350000000000000000),
    (22088330061790761/1250000000000000),
    (147943597238379/7812500000000),
    (388890275319/19531250000)]

private def fourRowFinite50Block11WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block11WeightEntryChunk0]

def fourRowFinite50Block11WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block11WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block11Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite50Block11WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite50Block11FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
