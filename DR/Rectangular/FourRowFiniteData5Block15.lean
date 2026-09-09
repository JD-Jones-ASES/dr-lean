import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 3, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block15PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(12583/15000), (164207/75000), (-2703453/250000), (13515341/937500), (-68024699/7500000), (3674743/1250000), (-1172109/2500000), (1449/50000), 0, 0]]

private def fourRowFinite5Block15PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block15PowerEntryChunk0]

def fourRowFinite5Block15PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block15PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block15Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block15PowerEntry (1*i.val+j.val)

private def fourRowFinite5Block15BernsteinEntryChunk0 : Array (ℚ) :=
  #[(301002972837/312500000000),
    (2514103109857/2500000000000),
    (4452369906931/5000000000000),
    (49966439177787/70000000000000),
    (930651994099/1750000000000),
    (4664667511/12500000000),
    (9720279/39062500),
    (31822463/200000000),
    (1235419/12500000),
    (3801/62500)]

private def fourRowFinite5Block15BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block15BernsteinEntryChunk0]

def fourRowFinite5Block15BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block15BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block15Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite5Block15BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite5Block15FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite5Block15FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block15FactorEntryChunk0]

def fourRowFinite5Block15FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block15FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block15WeightEntryChunk0 : Array (ℚ) :=
  #[(301002972837/312500000000),
    (2514103109857/2500000000000),
    (4452369906931/5000000000000),
    (49966439177787/70000000000000),
    (930651994099/1750000000000),
    (4664667511/12500000000),
    (9720279/39062500),
    (31822463/200000000),
    (1235419/12500000),
    (3801/62500)]

private def fourRowFinite5Block15WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block15WeightEntryChunk0]

def fourRowFinite5Block15WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block15WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block15Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite5Block15WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite5Block15FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
