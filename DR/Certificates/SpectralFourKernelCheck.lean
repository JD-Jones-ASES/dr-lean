import DR.Certificates.SpectralFourDefinitions
import Mathlib.Tactic.FinCases

namespace DittertRybin.Certificates
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_0 : let s : Fin 33 := 0;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_1 : let s : Fin 33 := 1;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_2 : let s : Fin 33 := 2;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_3 : let s : Fin 33 := 3;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_4 : let s : Fin 33 := 4;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_5 : let s : Fin 33 := 5;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_6 : let s : Fin 33 := 6;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_7 : let s : Fin 33 := 7;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_8 : let s : Fin 33 := 8;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_9 : let s : Fin 33 := 9;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_10 : let s : Fin 33 := 10;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_11 : let s : Fin 33 := 11;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_12 : let s : Fin 33 := 12;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_13 : let s : Fin 33 := 13;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_14 : let s : Fin 33 := 14;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_15 : let s : Fin 33 := 15;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_16 : let s : Fin 33 := 16;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_17 : let s : Fin 33 := 17;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_18 : let s : Fin 33 := 18;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_19 : let s : Fin 33 := 19;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_20 : let s : Fin 33 := 20;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_21 : let s : Fin 33 := 21;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_22 : let s : Fin 33 := 22;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_23 : let s : Fin 33 := 23;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_24 : let s : Fin 33 := 24;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_25 : let s : Fin 33 := 25;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_26 : let s : Fin 33 := 26;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_27 : let s : Fin 33 := 27;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_28 : let s : Fin 33 := 28;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_29 : let s : Fin 33 := 29;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_30 : let s : Fin 33 := 30;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_31 : let s : Fin 33 := 31;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourMatrix_checks_32 : let s : Fin 33 := 32;
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  unfold spectralFourTableMatrix spectralFourShift Matrix
  decide +kernel

theorem spectralFourMatrix_checks : ∀ s : Fin 33,
    (∀ i j, spectralFourTableMatrix s i j = spectralFourTableMatrix s j i) ∧
    (∀ i, (∑ j, spectralFourTableMatrix s i j) = 0) ∧
    (∀ i j, spectralFourShift s i j = spectralFourShift s j i) ∧
    (∀ i, (∑ j, spectralFourShift s i j) = 0) := by
  intro s
  fin_cases s
  · exact spectralFourMatrix_checks_0
  · exact spectralFourMatrix_checks_1
  · exact spectralFourMatrix_checks_2
  · exact spectralFourMatrix_checks_3
  · exact spectralFourMatrix_checks_4
  · exact spectralFourMatrix_checks_5
  · exact spectralFourMatrix_checks_6
  · exact spectralFourMatrix_checks_7
  · exact spectralFourMatrix_checks_8
  · exact spectralFourMatrix_checks_9
  · exact spectralFourMatrix_checks_10
  · exact spectralFourMatrix_checks_11
  · exact spectralFourMatrix_checks_12
  · exact spectralFourMatrix_checks_13
  · exact spectralFourMatrix_checks_14
  · exact spectralFourMatrix_checks_15
  · exact spectralFourMatrix_checks_16
  · exact spectralFourMatrix_checks_17
  · exact spectralFourMatrix_checks_18
  · exact spectralFourMatrix_checks_19
  · exact spectralFourMatrix_checks_20
  · exact spectralFourMatrix_checks_21
  · exact spectralFourMatrix_checks_22
  · exact spectralFourMatrix_checks_23
  · exact spectralFourMatrix_checks_24
  · exact spectralFourMatrix_checks_25
  · exact spectralFourMatrix_checks_26
  · exact spectralFourMatrix_checks_27
  · exact spectralFourMatrix_checks_28
  · exact spectralFourMatrix_checks_29
  · exact spectralFourMatrix_checks_30
  · exact spectralFourMatrix_checks_31
  · exact spectralFourMatrix_checks_32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_0 : let s : Fin 33 := 0;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_1 : let s : Fin 33 := 1;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_2 : let s : Fin 33 := 2;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_3 : let s : Fin 33 := 3;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_4 : let s : Fin 33 := 4;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_5 : let s : Fin 33 := 5;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_6 : let s : Fin 33 := 6;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_7 : let s : Fin 33 := 7;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_8 : let s : Fin 33 := 8;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_9 : let s : Fin 33 := 9;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_10 : let s : Fin 33 := 10;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_11 : let s : Fin 33 := 11;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_12 : let s : Fin 33 := 12;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_13 : let s : Fin 33 := 13;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_14 : let s : Fin 33 := 14;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_15 : let s : Fin 33 := 15;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_16 : let s : Fin 33 := 16;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_17 : let s : Fin 33 := 17;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_18 : let s : Fin 33 := 18;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_19 : let s : Fin 33 := 19;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_20 : let s : Fin 33 := 20;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_21 : let s : Fin 33 := 21;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_22 : let s : Fin 33 := 22;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_23 : let s : Fin 33 := 23;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_24 : let s : Fin 33 := 24;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_25 : let s : Fin 33 := 25;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_26 : let s : Fin 33 := 26;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_27 : let s : Fin 33 := 27;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_28 : let s : Fin 33 := 28;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_29 : let s : Fin 33 := 29;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_30 : let s : Fin 33 := 30;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_31 : let s : Fin 33 := 31;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem spectralFourFactor_checks_32 : let s : Fin 33 := 32;
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  decide +kernel

theorem spectralFourFactor_checks : ∀ s : Fin 33,
    (∀ a, 0 < (spectralFourCertificate s).weights a) ∧
    (∀ i j, i < j → (spectralFourCertificate s).factor j i = 0) ∧
    (∀ i, 0 < (spectralFourCertificate s).factor i i) := by
  intro s
  fin_cases s
  · exact spectralFourFactor_checks_0
  · exact spectralFourFactor_checks_1
  · exact spectralFourFactor_checks_2
  · exact spectralFourFactor_checks_3
  · exact spectralFourFactor_checks_4
  · exact spectralFourFactor_checks_5
  · exact spectralFourFactor_checks_6
  · exact spectralFourFactor_checks_7
  · exact spectralFourFactor_checks_8
  · exact spectralFourFactor_checks_9
  · exact spectralFourFactor_checks_10
  · exact spectralFourFactor_checks_11
  · exact spectralFourFactor_checks_12
  · exact spectralFourFactor_checks_13
  · exact spectralFourFactor_checks_14
  · exact spectralFourFactor_checks_15
  · exact spectralFourFactor_checks_16
  · exact spectralFourFactor_checks_17
  · exact spectralFourFactor_checks_18
  · exact spectralFourFactor_checks_19
  · exact spectralFourFactor_checks_20
  · exact spectralFourFactor_checks_21
  · exact spectralFourFactor_checks_22
  · exact spectralFourFactor_checks_23
  · exact spectralFourFactor_checks_24
  · exact spectralFourFactor_checks_25
  · exact spectralFourFactor_checks_26
  · exact spectralFourFactor_checks_27
  · exact spectralFourFactor_checks_28
  · exact spectralFourFactor_checks_29
  · exact spectralFourFactor_checks_30
  · exact spectralFourFactor_checks_31
  · exact spectralFourFactor_checks_32

end DittertRybin.Certificates
