import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=50, triple seed 0, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite50Block3PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(2961999/25000000), (45795418397/15000000000), (3436703724667/187500000000), (-1206804936248353/37500000000000), (340036534898773/18750000000000), (-35020565926073/18750000000000), (2439647580947/37500000000000), (-867540049/1250000000000), 0, 0]]

private def fourRowFinite50Block3PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite50Block3PowerEntryChunk0]

def fourRowFinite50Block3PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite50Block3PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite50Block3Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite50Block3PowerEntry (1*i.val+j.val)

private def fourRowFinite50Block3BernsteinEntryChunk0 : Array (ℚ) :=
  #[(360429415750697349/625000000000000000),
    (14489853808402779231/12500000000000000000),
    (49023341967594640641/25000000000000000000),
    (967392894861506499153/350000000000000000000),
    (3762504063553896663/1093750000000000000),
    (6898032780606256533/1750000000000000000),
    (1503173865670523619/350000000000000000),
    (5737364322571839/1250000000000000),
    (621943858635051/125000000000000),
    (8829704687601/1562500000000)]

private def fourRowFinite50Block3BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block3BernsteinEntryChunk0]

def fourRowFinite50Block3BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block3BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block3Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite50Block3BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite50Block3FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite50Block3FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block3FactorEntryChunk0]

def fourRowFinite50Block3FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block3FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite50Block3WeightEntryChunk0 : Array (ℚ) :=
  #[(360429415750697349/625000000000000000),
    (14489853808402779231/12500000000000000000),
    (49023341967594640641/25000000000000000000),
    (967392894861506499153/350000000000000000000),
    (3762504063553896663/1093750000000000000),
    (6898032780606256533/1750000000000000000),
    (1503173865670523619/350000000000000000),
    (5737364322571839/1250000000000000),
    (621943858635051/125000000000000),
    (8829704687601/1562500000000)]

private def fourRowFinite50Block3WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block3WeightEntryChunk0]

def fourRowFinite50Block3WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block3WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block3Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite50Block3WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite50Block3FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
