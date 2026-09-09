import DR.Square.OrderFourOrbitData

/-!
# Complete coverage of the 3,876 unordered quartic multipliers

Each gate checks actual cells under explicit bijective row and column maps.
Neither a canonical-key match nor a table index alone is used as evidence
that a multiplier belongs to its claimed seed orbit.
-/

namespace DittertRybin

open Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 32000000

def orderFourOrbitWitnessValid (a b c d : Fin 16) : Prop :=
  let w := orderFourOrbitWitness a b c d
  ((spectralFourMultipliers.get w.1).map (orderFourCellMapNat
    (orderFourLabelPermutation w.2.1) (orderFourLabelPermutation w.2.2))).toList.Perm
      [a.val, b.val, c.val, d.val]

noncomputable instance (a b c d : Fin 16) : Decidable (orderFourOrbitWitnessValid a b c d) :=
  inferInstanceAs (Decidable (List.Perm _ _))

theorem orderFourOrbitCoverage_0 : ∀ b c d : Fin 16,
    0 ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 0 b c d := by decide +kernel

theorem orderFourOrbitCoverage_1 : ∀ b c d : Fin 16,
    (1 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 1 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_2 : ∀ b c d : Fin 16,
    (2 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 2 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_3 : ∀ b c d : Fin 16,
    (3 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 3 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_4 : ∀ b c d : Fin 16,
    (4 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 4 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_5 : ∀ b c d : Fin 16,
    (5 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 5 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_6 : ∀ b c d : Fin 16,
    (6 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 6 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_7 : ∀ b c d : Fin 16,
    (7 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 7 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_8 : ∀ b c d : Fin 16,
    (8 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 8 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_9 : ∀ b c d : Fin 16,
    (9 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 9 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_10 : ∀ b c d : Fin 16,
    (10 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 10 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_11 : ∀ b c d : Fin 16,
    (11 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 11 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_12 : ∀ b c d : Fin 16,
    (12 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 12 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_13 : ∀ b c d : Fin 16,
    (13 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 13 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_14 : ∀ b c d : Fin 16,
    (14 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 14 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage_15 : ∀ b c d : Fin 16,
    (15 : Fin 16) ≤ b → b ≤ c → c ≤ d → orderFourOrbitWitnessValid 15 b c d := by
  decide +kernel

theorem orderFourOrbitCoverage (a b c d : Fin 16)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    orderFourOrbitWitnessValid a b c d := by
  fin_cases a
  · exact orderFourOrbitCoverage_0 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_1 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_2 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_3 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_4 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_5 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_6 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_7 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_8 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_9 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_10 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_11 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_12 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_13 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_14 b c d hab hbc hcd
  · exact orderFourOrbitCoverage_15 b c d hab hbc hcd

end DittertRybin
