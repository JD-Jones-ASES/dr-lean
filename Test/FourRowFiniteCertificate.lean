import DR.Rectangular.FourRowFiniteRole

namespace DittertRybin
open scoped BigOperators
open Certificates MvPolynomial
noncomputable section

example (a : FourRowFiniteCell 5) :
    fourRowFiniteTripleWeight (fun _ => a) = 1 :=
  fourRowFiniteTripleWeight_repeat a

example : fourRowFiniteTripleWeight
    (![(0,0), (0,0), (0,1)] : Fin 3 → FourRowFiniteCell 5) = 1/3 := by
  norm_num [fourRowFiniteTripleWeight, Matrix.cons_val_two, Fin.ext_iff]

example : fourRowFiniteTripleWeight
    (![(0,0), (0,1), (0,2)] : Fin 3 → FourRowFiniteCell 5) = 1/6 := by
  norm_num [fourRowFiniteTripleWeight, Matrix.cons_val_two, Fin.ext_iff]

example (a b c : FourRowFiniteCell 5) :
    fourRowFiniteFiveEquiv 5 ![a,a,b,c,a] = (![a,a,b], c,a) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

-- Repeating every physical cell does not lower the position-permutation factor.
example (a : FourRowFiniteCell 5) :
    (∑ σ : Equiv.Perm (Fin 5), fourRowFiniteTripleWeight
      (fun i => (fun _ : Fin 5 => a) (σ (Fin.castAdd 2 i)))) = 120 := by
  simp [fourRowFiniteTripleWeight_repeat, Fintype.card_perm, Nat.factorial]

example : fourRowFiniteNormalizedKey [(7,9), (7,9), (2,4), (7,4), (2,9)] = 3780 := by
  decide

example : fourRowFiniteCanonicalRoleKey [(7,9), (7,9), (7,9)] (7,9) (7,9) = 0 := by
  decide

example {n : ℕ} (coeff : ℕ → ℚ) (m : Fin 3 → FourRowFiniteCell n)
    (r : Equiv.Perm (Fin 4)) (c : Equiv.Perm (Fin n)) :
    (fourRowFiniteRoleMatrix coeff (fourRowFinitePhysicalPermutation r c ∘ m)).submatrix
      (fourRowFinitePhysicalPermutation r c) (fourRowFinitePhysicalPermutation r c) =
      fourRowFiniteRoleMatrix coeff m :=
  fourRowFiniteRoleMatrix_physical coeff m r c

-- The signed evaluation identity itself has no probability premise.
example {n : ℕ}
    (Q : (Fin 3 → FourRowFiniteCell n) → Matrix (FourRowFiniteCell n) (FourRowFiniteCell n) ℚ)
    (P : Board 4 n) :
    fourRowFinitePolynomialEval P (fourRowFiniteCertificatePolynomial Q) =
      ∑ m, (fourRowFiniteTripleWeight m : ℝ) * (∏ t, P (m t).1 (m t).2) *
        quadraticValue ((Q m).map (fun q : ℚ => (q : ℝ))) (fun a => P a.1 a.2) :=
  fourRowFiniteCertificatePolynomial_eval Q P

#print axioms fourRowFiniteWeightedPolynomial_eq_of_permutation_sums
#print axioms fourRowFiniteCertificatePolynomial_eval
#print axioms fourRowFiniteCertificatePolynomial_nonneg
#print axioms fourRowFiniteCertificatePolynomial_zero_iff
#print axioms fourRowFiniteRoleMatrix_physical

end
end DittertRybin
