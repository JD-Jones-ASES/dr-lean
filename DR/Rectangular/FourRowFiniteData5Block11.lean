import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 2, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block11PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(6469/10000), (999057/100000), (-21157417/500000), (84095141/1250000), (-135755897/2500000), (2334197/100000), (-1556721/312500), (251433/625000), 0, 0]]

private def fourRowFinite5Block11PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block11PowerEntryChunk0]

def fourRowFinite5Block11PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block11PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block11Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block11PowerEntry (1*i.val+j.val)

private def fourRowFinite5Block11BernsteinEntryChunk0 : Array (ℚ) :=
  #[(125476856967/97656250000),
    (632378211439/390625000000),
    (34667523936527/25000000000000),
    (17553901437213/17500000000000),
    (2299427217071/3500000000000),
    (2227562923/5468750000),
    (8717292459/35000000000),
    (154816609/1000000000),
    (1218493/12500000),
    (18483/312500)]

private def fourRowFinite5Block11BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block11BernsteinEntryChunk0]

def fourRowFinite5Block11BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block11BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block11Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite5Block11BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite5Block11FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite5Block11FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block11FactorEntryChunk0]

def fourRowFinite5Block11FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block11FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block11WeightEntryChunk0 : Array (ℚ) :=
  #[(125476856967/97656250000),
    (632378211439/390625000000),
    (34667523936527/25000000000000),
    (17553901437213/17500000000000),
    (2299427217071/3500000000000),
    (2227562923/5468750000),
    (8717292459/35000000000),
    (154816609/1000000000),
    (1218493/12500000),
    (18483/312500)]

private def fourRowFinite5Block11WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block11WeightEntryChunk0]

def fourRowFinite5Block11WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block11WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block11Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite5Block11WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite5Block11FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
