import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=50, triple seed 5, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite50Block23PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(-23178867/50000000), (653428177/2500000000), (10007959891363/125000000000), (-631207716892073/6250000000000), (196639271372/6103515625), (-9105656384899/3125000000000), (301068646753/3125000000000), (-6269697813/6250000000000), 0, 0]]

private def fourRowFinite50Block23PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite50Block23PowerEntryChunk0]

def fourRowFinite50Block23PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite50Block23PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite50Block23Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite50Block23PowerEntry (1*i.val+j.val)

private def fourRowFinite50Block23BernsteinEntryChunk0 : Array (ℚ) :=
  #[(16587252478105455447/62500000000000000000),
    (25040138802744451029/15625000000000000000),
    (1025577818361107177583/250000000000000000000),
    (34987372284120297543/5000000000000000000),
    (16942028120362929057/1750000000000000000),
    (10231662847474045977/875000000000000000),
    (555976413119299527/43750000000000000),
    (7825757155364121/625000000000000),
    (43121459254647/3906250000000),
    (16146768267/1953125000)]

private def fourRowFinite50Block23BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block23BernsteinEntryChunk0]

def fourRowFinite50Block23BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block23BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block23Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite50Block23BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite50Block23FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite50Block23FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block23FactorEntryChunk0]

def fourRowFinite50Block23FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block23FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite50Block23WeightEntryChunk0 : Array (ℚ) :=
  #[(16587252478105455447/62500000000000000000),
    (25040138802744451029/15625000000000000000),
    (1025577818361107177583/250000000000000000000),
    (34987372284120297543/5000000000000000000),
    (16942028120362929057/1750000000000000000),
    (10231662847474045977/875000000000000000),
    (555976413119299527/43750000000000000),
    (7825757155364121/625000000000000),
    (43121459254647/3906250000000),
    (16146768267/1953125000)]

private def fourRowFinite50Block23WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block23WeightEntryChunk0]

def fourRowFinite50Block23WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block23WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block23Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite50Block23WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite50Block23FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
