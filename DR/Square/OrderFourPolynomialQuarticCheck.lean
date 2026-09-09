import DR.Square.OrderFourPolynomialSymmetry
import DR.Square.OrderFourPolynomialQuarticCoefficients

namespace DittertRybin

open Certificates MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

noncomputable def orderFourQuarticSeedList (s : Fin 33) : List (Fin 16) :=
  (spectralFourMultipliers.get s).toList.map
    (fun a => (⟨a % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16))

def orderFourQuarticListSuccess (l : List (Fin 16)) : Prop :=
  (l.map (fun a => a.val / 4)).Nodup ∨ (l.map (fun a => a.val % 4)).Nodup

instance (l : List (Fin 16)) : Decidable (orderFourQuarticListSuccess l) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem orderFourQuarticCoefficient_seed_0 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 0 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 0) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_32 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 32 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 32) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_1 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 1 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 1) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_2 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 2 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 2) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_3 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 3 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 3) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_4 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 4 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 4) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_5 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 5 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 5) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_6 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 6 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 6) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_7 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 7 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 7) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_8 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 8 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 8) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_9 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 9 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 9) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_10 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 10 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 10) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_11 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 11 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 11) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_12 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 12 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 12) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_13 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 13 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 13) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_14 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 14 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 14) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_15 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 15 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 15) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_16 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 16 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 16) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_17 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 17 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 17) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_18 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 18 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 18) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_19 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 19 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 19) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_20 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 20 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 20) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_21 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 21 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 21) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_22 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 22 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 22) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_23 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 23 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 23) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_24 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 24 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 24) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_25 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 25 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 25) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_26 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 26 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 26) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_27 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 27 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 27) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_28 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 28 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 28) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_29 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 29 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 29) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_30 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 30 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 30) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed_31 :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList 31 : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList 31) then (24:ℚ) else 0 := by
  rw [orderFourQuarticPolynomial_coeff_compute]
  decide +kernel

theorem orderFourQuarticCoefficient_seed (s : Fin 33) :
    coeff (Multiset.toFinsupp (orderFourQuarticSeedList s : Multiset (Fin 16)))
        orderFourQuarticPolynomial =
      if orderFourQuarticListSuccess (orderFourQuarticSeedList s) then (24:ℚ) else 0 := by
  fin_cases s
  · exact orderFourQuarticCoefficient_seed_0
  · exact orderFourQuarticCoefficient_seed_1
  · exact orderFourQuarticCoefficient_seed_2
  · exact orderFourQuarticCoefficient_seed_3
  · exact orderFourQuarticCoefficient_seed_4
  · exact orderFourQuarticCoefficient_seed_5
  · exact orderFourQuarticCoefficient_seed_6
  · exact orderFourQuarticCoefficient_seed_7
  · exact orderFourQuarticCoefficient_seed_8
  · exact orderFourQuarticCoefficient_seed_9
  · exact orderFourQuarticCoefficient_seed_10
  · exact orderFourQuarticCoefficient_seed_11
  · exact orderFourQuarticCoefficient_seed_12
  · exact orderFourQuarticCoefficient_seed_13
  · exact orderFourQuarticCoefficient_seed_14
  · exact orderFourQuarticCoefficient_seed_15
  · exact orderFourQuarticCoefficient_seed_16
  · exact orderFourQuarticCoefficient_seed_17
  · exact orderFourQuarticCoefficient_seed_18
  · exact orderFourQuarticCoefficient_seed_19
  · exact orderFourQuarticCoefficient_seed_20
  · exact orderFourQuarticCoefficient_seed_21
  · exact orderFourQuarticCoefficient_seed_22
  · exact orderFourQuarticCoefficient_seed_23
  · exact orderFourQuarticCoefficient_seed_24
  · exact orderFourQuarticCoefficient_seed_25
  · exact orderFourQuarticCoefficient_seed_26
  · exact orderFourQuarticCoefficient_seed_27
  · exact orderFourQuarticCoefficient_seed_28
  · exact orderFourQuarticCoefficient_seed_29
  · exact orderFourQuarticCoefficient_seed_30
  · exact orderFourQuarticCoefficient_seed_31
  · exact orderFourQuarticCoefficient_seed_32

end DittertRybin
