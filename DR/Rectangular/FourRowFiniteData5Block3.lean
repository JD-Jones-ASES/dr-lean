import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 0, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block3PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(-6307/30000), (807671/75000), (-26483777/750000), (7692083/156250), (-1700426/46875), (27383743/1875000), (-1395487/468750), (36449/156250), 0, 0]]

private def fourRowFinite5Block3PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block3PowerEntryChunk0]

def fourRowFinite5Block3PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block3PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block3Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block3PowerEntry (1*i.val+j.val)

private def fourRowFinite5Block3BernsteinEntryChunk0 : Array (ℚ) :=
  #[(27309040787/48828125000),
    (1246687493659/1171875000000),
    (19882310943263/18750000000000),
    (235816770083/273437500000),
    (1654385950367/2625000000000),
    (22645654541/52500000000),
    (707133777/2500000000),
    (269013383/1500000000),
    (2044379/18750000),
    (9607/156250)]

private def fourRowFinite5Block3BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block3BernsteinEntryChunk0]

def fourRowFinite5Block3BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block3BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block3Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite5Block3BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite5Block3FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite5Block3FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block3FactorEntryChunk0]

def fourRowFinite5Block3FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block3FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block3WeightEntryChunk0 : Array (ℚ) :=
  #[(27309040787/48828125000),
    (1246687493659/1171875000000),
    (19882310943263/18750000000000),
    (235816770083/273437500000),
    (1654385950367/2625000000000),
    (22645654541/52500000000),
    (707133777/2500000000),
    (269013383/1500000000),
    (2044379/18750000),
    (9607/156250)]

private def fourRowFinite5Block3WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block3WeightEntryChunk0]

def fourRowFinite5Block3WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block3WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block3Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite5Block3WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite5Block3FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
