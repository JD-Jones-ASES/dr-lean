import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 6, interaction sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block27PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(-1033/7500), (216673/37500), (-5613909/250000), (49093939/1250000), (-9065517/250000), (13250479/750000), (-312119/75000), (56203/156250), 0, 0]]

private def fourRowFinite5Block27PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block27PowerEntryChunk0]

def fourRowFinite5Block27PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block27PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block27Power : Fin 1 → Fin 1 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block27PowerEntry (1*i.val+j.val)

private def fourRowFinite5Block27BernsteinEntryChunk0 : Array (ℚ) :=
  #[(98174400457/390625000000),
    (4539259554119/9375000000000),
    (16192011183907/37500000000000),
    (5665040835233/17500000000000),
    (1278691821073/5250000000000),
    (10517955179/52500000000),
    (6133342113/35000000000),
    (111251041/750000000),
    (20663/187500),
    (4928/78125)]

private def fourRowFinite5Block27BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block27BernsteinEntryChunk0]

def fourRowFinite5Block27BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block27BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block27Bernstein (k : Fin 10) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => fourRowFinite5Block27BernsteinEntry (1*k.val+1*i.val+j.val)

private def fourRowFinite5Block27FactorEntryChunk0 : Array (ℚ) :=
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

private def fourRowFinite5Block27FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block27FactorEntryChunk0]

def fourRowFinite5Block27FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block27FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block27WeightEntryChunk0 : Array (ℚ) :=
  #[(98174400457/390625000000),
    (4539259554119/9375000000000),
    (16192011183907/37500000000000),
    (5665040835233/17500000000000),
    (1278691821073/5250000000000),
    (10517955179/52500000000),
    (6133342113/35000000000),
    (111251041/750000000),
    (20663/187500),
    (4928/78125)]

private def fourRowFinite5Block27WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block27WeightEntryChunk0]

def fourRowFinite5Block27WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block27WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block27Gram (k : Fin 10) : GramCertificate 1 1 where
  weights i := fourRowFinite5Block27WeightEntry (1*k.val+i.val)
  factor i j := fourRowFinite5Block27FactorEntry (1*k.val+1*i.val+j.val)

end
end DittertRybin
