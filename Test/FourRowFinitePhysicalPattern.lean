import DR.Rectangular.FourRowFinitePhysicalPattern

/-! Equality-pattern controls: repeats, noncontiguous ordinary labels, one or
no ordinary label, empty distinguished index set, and a rejected collapse. -/
namespace DittertRybin
open Certificates

example : fourRowFinitePhysicalFiveLabels ![0,1,0]
    (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) = ![0,1,0,9,4] := by
  decide +kernel
example : fourRowFiniteCompressedFiveLabels ![0,1,0]
    (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) = ![0,1,0,2,3] := by
  decide +kernel
example : fourRowFiniteCompressedFiveLabels ![0,1,0]
    (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 7) = ![0,1,0,2,2] := by
  decide +kernel
example (i j : Fin 5) :
    fourRowFinitePhysicalFiveLabels ![0,1,0]
      (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) i =
    fourRowFinitePhysicalFiveLabels ![0,1,0]
      (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) j ↔
    fourRowFiniteCompressedFiveLabels ![0,1,0]
      (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) i =
    fourRowFiniteCompressedFiveLabels ![0,1,0]
      (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) j :=
  fourRowFinitePhysicalFiveLabels_eq_iff _ _ _ i j

example : fourRowFiniteCompressedFiveLabels (fun _ => 0)
    (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 0) (Sum.inl 0) = ![0,0,0,0,0] := by
  decide +kernel
example : fourRowFiniteCompressedFiveLabels (fun _ => 0)
    (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1) (Sum.inr 0) = ![0,0,0,1,1] := by
  decide +kernel
example : fourRowFinitePairLabels
    (ordinaryPair (Sum.inr (0 : Fin 2) : Fin 0 ⊕ Fin 2) (Sum.inr 1)) = (0,1) := by
  decide +kernel

/-- Distinct ordinary labels cannot both be represented by the same label. -/
example : ¬ (∀ i j : Fin 5,
    fourRowFinitePhysicalFiveLabels ![0,1,0]
      (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) i =
    fourRowFinitePhysicalFiveLabels ![0,1,0]
      (Sum.inr (7 : Fin 10) : Fin 2 ⊕ Fin 10) (Sum.inr 2) j ↔
    (![0,1,0,2,2] : Fin 5 → ℕ) i = (![0,1,0,2,2] : Fin 5 → ℕ) j) := by
  decide +kernel

#print axioms fourRowFinitePairLabels_fst_distinguished
#print axioms fourRowFinitePairLabels_snd_distinguished
#print axioms fourRowFinitePairLabels_eq_iff
#print axioms fourRowFinitePhysicalFiveLabels_eq_iff
end DittertRybin
