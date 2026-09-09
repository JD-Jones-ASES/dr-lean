import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=50, triple seed 3, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite50Block15PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(50605471/75000000), (85652777449/3750000000), (954518542687/375000000000), (-114199597728551/9375000000000), (-72421140272857/37500000000000), (205444793959/585937500000), (-265979665993/18750000000000), (2010632161/12500000000000), 0, 0]]

private def fourRowFinite50Block15PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite50Block15PowerEntryChunk0]

def fourRowFinite50Block15PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite50Block15PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite50Block15Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite50Block15PowerEntry (1*i.val+j.val)

private def fourRowFinite50Block15BernsteinEntryChunk0 : Array (ℚ) :=
  #[(371487073133525005741/125000000000000000000),
    (494023067703466878361/93750000000000000000),
    (11309671269825151318847/1500000000000000000000),
    (676926772656173798407/70000000000000000000),
    (605855848135379412317/52500000000000000000),
    (34177877631561666761/2625000000000000000),
    (698780980340307831/50000000000000000),
    (214006041027129931/15000000000000000),
    (1031381834790283/75000000000000),
    (19195223852063/1562500000000)]

private def fourRowFinite50Block15BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block15BernsteinEntryChunk0]

def fourRowFinite50Block15BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block15BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block15Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite50Block15BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite50Block15FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite50Block15FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block15FactorEntryChunk0]

def fourRowFinite50Block15FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block15FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite50Block15WeightEntryChunk0 : Array (ℚ) :=
  #[(371487073133525005741/125000000000000000000),
    (494023067703466878361/93750000000000000000),
    (11309671269825151318847/1500000000000000000000),
    (676926772656173798407/70000000000000000000),
    (605855848135379412317/52500000000000000000),
    (34177877631561666761/2625000000000000000),
    (698780980340307831/50000000000000000),
    (214006041027129931/15000000000000000),
    (1031381834790283/75000000000000),
    (19195223852063/1562500000000)]

private def fourRowFinite50Block15WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite50Block15WeightEntryChunk0]

def fourRowFinite50Block15WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite50Block15WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite50Block15Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite50Block15WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite50Block15FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
