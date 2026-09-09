import DR.Rectangular.FourRowFiniteBernsteinLinear

/-! Exact degree-nine transform for the interval [1/10,1], checked once. -/

set_option maxRecDepth 100000

namespace DittertRybin.Certificates
open scoped BigOperators

private def fourRowFiniteBernsteinNineEntryChunk0 : Array (ℚ) :=
  #[1,
    (1/10),
    (1/100),
    (1/1000),
    (1/10000),
    (1/100000),
    (1/1000000),
    (1/10000000),
    (1/100000000),
    (1/1000000000),
    1,
    (1/5),
    (3/100),
    (1/250),
    (1/2000),
    (3/50000),
    (7/1000000),
    (1/1250000),
    (9/100000000),
    (1/100000000),
    1,
    (3/10),
    (29/400),
    (11/800),
    (9/4000),
    (67/200000),
    (187/4000000),
    (249/40000000),
    (1/1250000),
    (1/10000000),
    1,
    (2/5)]

private def fourRowFiniteBernsteinNineEntryChunk1 : Array (ℚ) :=
  #[(11/80),
    (109/2800),
    (247/28000),
    (149/87500),
    (8227/28000000),
    (187/4000000),
    (7/1000000),
    (1/1000000),
    1,
    (1/2),
    (9/40),
    (247/2800),
    (809/28000),
    (1527/200000),
    (149/87500),
    (67/200000),
    (3/50000),
    (1/100000),
    1,
    (3/5),
    (67/200),
    (149/875),
    (1527/20000),
    (809/28000),
    (247/28000),
    (9/4000),
    (1/2000),
    (1/10000),
    1,
    (7/10),
    (187/400),
    (8227/28000)]

private def fourRowFiniteBernsteinNineEntryChunk2 : Array (ℚ) :=
  #[(149/875),
    (247/2800),
    (109/2800),
    (11/800),
    (1/250),
    (1/1000),
    1,
    (4/5),
    (249/400),
    (187/400),
    (67/200),
    (9/40),
    (11/80),
    (29/400),
    (3/100),
    (1/100),
    1,
    (9/10),
    (4/5),
    (7/10),
    (3/5),
    (1/2),
    (2/5),
    (3/10),
    (1/5),
    (1/10),
    1,
    1,
    1,
    1,
    1,
    1]

private def fourRowFiniteBernsteinNineEntryChunk3 : Array (ℚ) :=
  #[1,
    1,
    1,
    1]

private def fourRowFiniteBernsteinNineEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFiniteBernsteinNineEntryChunk0, fourRowFiniteBernsteinNineEntryChunk1, fourRowFiniteBernsteinNineEntryChunk2, fourRowFiniteBernsteinNineEntryChunk3]

def fourRowFiniteBernsteinNineEntry (i : ℕ) : ℚ :=
  (fourRowFiniteBernsteinNineEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFiniteBernsteinNine (i j : Fin 10) : ℚ :=
  fourRowFiniteBernsteinNineEntry (10*i.val+j.val)

set_option maxHeartbeats 32000000 in
theorem fourRowFiniteBernsteinNine_exact : ∀ i j : Fin 10,
    fourRowFiniteBernsteinNine i j = fourRowFiniteBernsteinLinearMap (1/10) 1 i j := by
  decide +kernel

theorem fourRowFiniteBernsteinNine_apply (p : Fin 10 → ℚ) (i : Fin 10) :
    powerToBernstein (affinePowerCoefficients (1/10) 1 p) i =
      ∑ j, fourRowFiniteBernsteinNine i j*p j := by
  simpa only [fourRowFiniteBernsteinNine_exact] using
    fourRowFiniteBernsteinLinearMap_apply (1/10) 1 p i

end DittertRybin.Certificates
