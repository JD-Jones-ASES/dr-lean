import DR.Square.OrderFourOrbitAugmentedData

/-!
# Complete coverage of the 8,448 augmented quartic seeds

After the four-cell orbit reduction, these are all possibilities for the two
remaining physical cells. Each gate checks the actual six-cell multiset image.
-/

namespace DittertRybin

open Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

def orderFourAugmentedWitnessValid (t : Fin 33) (i j : Fin 16) : Prop :=
  let w := orderFourAugmentedWitness t i j
  ((orderFourSexticSeeds.get w.1).map (orderFourCellMapNat
    (orderFourLabelPermutation w.2.1) (orderFourLabelPermutation w.2.2))).toList.Perm
      ((spectralFourMultipliers.get t).toList ++ [i.val, j.val])

noncomputable instance (t : Fin 33) (i j : Fin 16) :
    Decidable (orderFourAugmentedWitnessValid t i j) :=
  inferInstanceAs (Decidable (List.Perm _ _))

theorem orderFourAugmentedCoverage_0 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 0 i j := by decide +kernel

theorem orderFourAugmentedCoverage_1 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 1 i j := by decide +kernel

theorem orderFourAugmentedCoverage_2 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 2 i j := by decide +kernel

theorem orderFourAugmentedCoverage_3 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 3 i j := by decide +kernel

theorem orderFourAugmentedCoverage_4 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 4 i j := by decide +kernel

theorem orderFourAugmentedCoverage_5 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 5 i j := by decide +kernel

theorem orderFourAugmentedCoverage_6 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 6 i j := by decide +kernel

theorem orderFourAugmentedCoverage_7 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 7 i j := by decide +kernel

theorem orderFourAugmentedCoverage_8 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 8 i j := by decide +kernel

theorem orderFourAugmentedCoverage_9 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 9 i j := by decide +kernel

theorem orderFourAugmentedCoverage_10 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 10 i j := by decide +kernel

theorem orderFourAugmentedCoverage_11 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 11 i j := by decide +kernel

theorem orderFourAugmentedCoverage_12 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 12 i j := by decide +kernel

theorem orderFourAugmentedCoverage_13 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 13 i j := by decide +kernel

theorem orderFourAugmentedCoverage_14 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 14 i j := by decide +kernel

theorem orderFourAugmentedCoverage_15 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 15 i j := by decide +kernel

theorem orderFourAugmentedCoverage_16 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 16 i j := by decide +kernel

theorem orderFourAugmentedCoverage_17 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 17 i j := by decide +kernel

theorem orderFourAugmentedCoverage_18 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 18 i j := by decide +kernel

theorem orderFourAugmentedCoverage_19 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 19 i j := by decide +kernel

theorem orderFourAugmentedCoverage_20 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 20 i j := by decide +kernel

theorem orderFourAugmentedCoverage_21 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 21 i j := by decide +kernel

theorem orderFourAugmentedCoverage_22 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 22 i j := by decide +kernel

theorem orderFourAugmentedCoverage_23 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 23 i j := by decide +kernel

theorem orderFourAugmentedCoverage_24 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 24 i j := by decide +kernel

theorem orderFourAugmentedCoverage_25 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 25 i j := by decide +kernel

theorem orderFourAugmentedCoverage_26 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 26 i j := by decide +kernel

theorem orderFourAugmentedCoverage_27 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 27 i j := by decide +kernel

theorem orderFourAugmentedCoverage_28 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 28 i j := by decide +kernel

theorem orderFourAugmentedCoverage_29 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 29 i j := by decide +kernel

theorem orderFourAugmentedCoverage_30 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 30 i j := by decide +kernel

theorem orderFourAugmentedCoverage_31 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 31 i j := by decide +kernel

theorem orderFourAugmentedCoverage_32 : ∀ i j : Fin 16,
    orderFourAugmentedWitnessValid 32 i j := by decide +kernel

theorem orderFourAugmentedCoverage (t : Fin 33) (i j : Fin 16) :
    orderFourAugmentedWitnessValid t i j := by
  fin_cases t
  · exact orderFourAugmentedCoverage_0 i j
  · exact orderFourAugmentedCoverage_1 i j
  · exact orderFourAugmentedCoverage_2 i j
  · exact orderFourAugmentedCoverage_3 i j
  · exact orderFourAugmentedCoverage_4 i j
  · exact orderFourAugmentedCoverage_5 i j
  · exact orderFourAugmentedCoverage_6 i j
  · exact orderFourAugmentedCoverage_7 i j
  · exact orderFourAugmentedCoverage_8 i j
  · exact orderFourAugmentedCoverage_9 i j
  · exact orderFourAugmentedCoverage_10 i j
  · exact orderFourAugmentedCoverage_11 i j
  · exact orderFourAugmentedCoverage_12 i j
  · exact orderFourAugmentedCoverage_13 i j
  · exact orderFourAugmentedCoverage_14 i j
  · exact orderFourAugmentedCoverage_15 i j
  · exact orderFourAugmentedCoverage_16 i j
  · exact orderFourAugmentedCoverage_17 i j
  · exact orderFourAugmentedCoverage_18 i j
  · exact orderFourAugmentedCoverage_19 i j
  · exact orderFourAugmentedCoverage_20 i j
  · exact orderFourAugmentedCoverage_21 i j
  · exact orderFourAugmentedCoverage_22 i j
  · exact orderFourAugmentedCoverage_23 i j
  · exact orderFourAugmentedCoverage_24 i j
  · exact orderFourAugmentedCoverage_25 i j
  · exact orderFourAugmentedCoverage_26 i j
  · exact orderFourAugmentedCoverage_27 i j
  · exact orderFourAugmentedCoverage_28 i j
  · exact orderFourAugmentedCoverage_29 i j
  · exact orderFourAugmentedCoverage_30 i j
  · exact orderFourAugmentedCoverage_31 i j
  · exact orderFourAugmentedCoverage_32 i j

end DittertRybin
