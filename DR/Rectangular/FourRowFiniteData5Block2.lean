import DR.Rectangular.FourRowFiniteBernstein
import DR.Certificates.StrictGram

/-! Generated exact data, scripts/generate_four_row_finite.py.
Family a=5, triple seed 0, column sector.
Gram and Bernstein gates are in the separate Checks module. -/

set_option maxRecDepth 100000

namespace DittertRybin
open Certificates
noncomputable section

private def fourRowFinite5Block2PowerEntryChunk0 : Array (Fin 10 → ℚ) :=
  #[![(217/3000), (124589/20000), (-622429/37500), (10694799/500000), (-26356801/1500000), (10780021/1250000), (-5310333/2500000), (47781/250000), 0, 0],
    ![(-4537/40000), (105979/150000), (5811427/1500000), (-9196049/937500), (5751757/750000), (-18662839/7500000), (1586563/5000000), (-27171/2500000), 0, 0],
    ![(-4537/40000), (105979/150000), (5811427/1500000), (-9196049/937500), (5751757/750000), (-18662839/7500000), (1586563/5000000), (-27171/2500000), 0, 0],
    ![(16493/90000), (183397/450000), (25299761/4500000), (-40362059/2500000), (44905751/2812500), (-164606597/22500000), (35273381/22500000), (-467381/3750000), 0, 0]]

private def fourRowFinite5Block2PowerEntryChunks : Array (Array (Fin 10 → ℚ)) :=
  #[fourRowFinite5Block2PowerEntryChunk0]

def fourRowFinite5Block2PowerEntry (i : ℕ) : Fin 10 → ℚ :=
  (fourRowFinite5Block2PowerEntryChunks.getD (i / 32) #[]).getD (i % 32) (fun _ => 0)

def fourRowFinite5Block2Power : Fin 2 → Fin 2 → Fin 10 → ℚ :=
  fun i j => fourRowFinite5Block2PowerEntry (2*i.val+j.val)

private def fourRowFinite5Block2BernsteinEntryChunk0 : Array (ℚ) :=
  #[(171566837421/312500000000),
    (-40925850707/3125000000000),
    (-40925850707/3125000000000),
    (1245057926413/4687500000000),
    (2243889124937/2500000000000),
    (8141985903611/75000000000000),
    (8141985903611/75000000000000),
    (42345706522091/112500000000000),
    (4975841515739/5000000000000),
    (39146952584939/150000000000000),
    (39146952584939/150000000000000),
    (29513388607841/56250000000000),
    (68152514951259/70000000000000),
    (7671036226349/20000000000000),
    (7671036226349/20000000000000),
    (130131255062051/210000000000000),
    (1564432714853/1750000000000),
    (29489609707/65625000000),
    (29489609707/65625000000),
    (20030937634937/31500000000000),
    (27344940977/35000000000),
    (190860907823/420000000000),
    (190860907823/420000000000),
    (114816196597/196875000000),
    (9052837041/14000000000),
    (7155009633/17500000000),
    (7155009633/17500000000),
    (34021832183/70000000000),
    (49904873/100000000),
    (1979105503/6000000000),
    (1979105503/6000000000),
    (3335592151/9000000000)]

private def fourRowFinite5Block2BernsteinEntryChunk1 : Array (ℚ) :=
  #[(546943/1562500),
    (709123/3000000),
    (709123/3000000),
    (29032801/112500000),
    (16647/78125),
    (90839/625000),
    (90839/625000),
    (30349/187500)]

private def fourRowFinite5Block2BernsteinEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block2BernsteinEntryChunk0, fourRowFinite5Block2BernsteinEntryChunk1]

def fourRowFinite5Block2BernsteinEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block2BernsteinEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block2Bernstein (k : Fin 10) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => fourRowFinite5Block2BernsteinEntry (4*k.val+2*i.val+j.val)

private def fourRowFinite5Block2FactorEntryChunk0 : Array (ℚ) :=
  #[744971070,
    -17770669,
    0,
    1,
    67316673748110,
    8141985903611,
    0,
    1,
    149275245472170,
    39146952584939,
    0,
    1,
    136305029902518,
    53697253584443,
    0,
    1,
    4693298144559,
    2359168776560,
    0,
    1,
    328139291724,
    190860907823,
    0,
    1,
    15088061735,
    9540012844,
    0,
    1,
    2994292380,
    1979105503,
    0,
    1]

private def fourRowFinite5Block2FactorEntryChunk1 : Array (ℚ) :=
  #[26253264,
    17728075,
    0,
    1,
    133176,
    90839,
    0,
    1]

private def fourRowFinite5Block2FactorEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block2FactorEntryChunk0, fourRowFinite5Block2FactorEntryChunk1]

def fourRowFinite5Block2FactorEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block2FactorEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

private def fourRowFinite5Block2WeightEntryChunk0 : Array (ℚ) :=
  #[(2303/2328034593750000000000),
    (205875825784930578319/776011531250000000000),
    (1/5048750531108250000000000000),
    (1834089472599275520806826019/5048750531108250000000000000),
    (1/22391286820825500000000000000),
    (10215831647715233466015126199/22391286820825500000000000000),
    (1/19082704186352520000000000000),
    (8941634699144728995315809363/19082704186352520000000000000),
    (1/24639815258934750000000000),
    (20205699512684407520752061/49279630517869500000000000),
    (1/137818502524080000000000),
    (219734760575921423677787/689092512620400000000000),
    (3/1056164321450000000000),
    (240287969123858912497/1056164321450000000000),
    (1/17965754280000000000),
    (2741633515013189911/17965754280000000000),
    (1/1968994800000000),
    (193852549669351/1968994800000000),
    (1/83235000000),
    (1740268053/27745000000)]

private def fourRowFinite5Block2WeightEntryChunks : Array (Array (ℚ)) :=
  #[fourRowFinite5Block2WeightEntryChunk0]

def fourRowFinite5Block2WeightEntry (i : ℕ) : ℚ :=
  (fourRowFinite5Block2WeightEntryChunks.getD (i / 32) #[]).getD (i % 32) (0)

def fourRowFinite5Block2Gram (k : Fin 10) : GramCertificate 2 2 where
  weights i := fourRowFinite5Block2WeightEntry (2*k.val+i.val)
  factor i j := fourRowFinite5Block2FactorEntry (4*k.val+2*i.val+j.val)

end
end DittertRybin
