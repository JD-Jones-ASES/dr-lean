import DR.Endpoint.TwoZeroMixedCoefficients
import DR.Square.OrderThree

namespace DittertRybin.Tests

private noncomputable def signedMixedThree : Board 3 3 :=
  fun i j => if i.val=0 then (if j.val=0 then 1 else if j.val=1 then 2 else 3)
    else if i.val=1 then (if j.val=0 then -1 else if j.val=1 then 0 else 2)
    else (if j.val=0 then 3 else if j.val=1 then 4 else 5)

private theorem signedMixedThree_permanent : signedMixedThree.permanent = -2 := by
  have h := permanent_three signedMixedThree
  norm_num [signedMixedThree] at h
  exact h

private theorem signedMixedThree_first :
    (signedMixedThree.updateRow (Fin.natAdd 1 (1 : Fin 2)) (signedMixedThree (Fin.natAdd 1 (0 : Fin 2)))).permanent = -8 := by
  have h := permanent_three (signedMixedThree.updateRow (Fin.natAdd 1 (1 : Fin 2)) (signedMixedThree (Fin.natAdd 1 (0 : Fin 2))))
  norm_num [signedMixedThree,Matrix.updateRow,Matrix.of_apply,Function.update,Fin.natAdd,Fin.ext_iff] at h
  exact h

private theorem signedMixedThree_second :
    (signedMixedThree.updateRow (Fin.natAdd 1 (0 : Fin 2)) (signedMixedThree (Fin.natAdd 1 (1 : Fin 2)))).permanent = 172 := by
  have h := permanent_three (signedMixedThree.updateRow (Fin.natAdd 1 (0 : Fin 2)) (signedMixedThree (Fin.natAdd 1 (1 : Fin 2))))
  norm_num [signedMixedThree,Matrix.updateRow,Matrix.of_apply,Function.update,Fin.natAdd,Fin.ext_iff] at h
  exact h

-- All three exact coefficients are compared with actual signed permanents.
example : (permanentMixedQuadratic signedMixedThree).coeff (Finsupp.single (0 : Fin 2) 2) = -4 ∧
    (permanentMixedQuadratic signedMixedThree).coeff (squarefreeExponent 2) = -2 ∧
    (permanentMixedQuadratic signedMixedThree).coeff (Finsupp.single (1 : Fin 2) 2) = 86 := by
  rw [permanentMixedQuadratic_coeff20,permanentMixedQuadratic_coeff11,permanentMixedQuadratic_coeff02]
  rw [signedMixedThree_first,signedMixedThree_permanent,signedMixedThree_second]
  norm_num

-- Omitting the division by two is a rejected mutation on an actual matrix.
example : ¬(permanentMixedQuadratic signedMixedThree).coeff (Finsupp.single (0 : Fin 2) 2) =
    (signedMixedThree.updateRow (Fin.natAdd 1 (1 : Fin 2)) (signedMixedThree (Fin.natAdd 1 (0 : Fin 2)))).permanent := by
  rw [permanentMixedQuadratic_coeff20,signedMixedThree_first]
  norm_num

-- The empty eliminated prefix remains part of the exact algebraic statement.
example (p : MvPolynomial (Fin 2) ℝ) : permanentQuadraticReduce 0 p = p := rfl

example (A : Board 2 2) : (permanentMixedQuadratic A).coeff (Finsupp.single (0 : Fin 2) 2) =
    (A.updateRow 1 (A 0)).permanent/2 := by
  simpa using permanentMixedQuadratic_coeff20 (n := 0) A

-- Restored exponents put one in each eliminated coordinate, not a factorial.
example (d : Fin 2 →₀ ℕ) : permanentQuadraticExponent 2 d 0=1 ∧
    permanentQuadraticExponent 2 d (0 : Fin 3).succ=1 ∧
    permanentQuadraticExponent 2 d (0 : Fin 2).succ.succ=d 0 ∧
    permanentQuadraticExponent 2 d (1 : Fin 2).succ.succ=d 1 := by
  simp only [permanentQuadraticExponent,Finsupp.cons_zero,Finsupp.cons_succ]
  trivial

-- Row duplication has an exact polynomial meaning even for signed entries.
example : permanentMixedQuadratic (signedMixedThree.updateRow 2 (signedMixedThree 1)) =
    (permanentMixedQuadratic signedMixedThree).eval₂ MvPolynomial.C (repeatPolynomialVariable 0 1) := by
  simpa using permanentMixedQuadratic_repeat_row signedMixedThree 0 1 (by decide)

-- Nonnegativity is essential to the permanent inequality, not to the identities.
private noncomputable def signedMixedCounterexample : Board 3 3 :=
  fun i j => if i.val=0 then -1
    else if i.val=1 then (if j.val=2 then 1 else -1)
    else (if j.val=0 then -1 else if j.val=1 then 1 else 0)

private theorem signedMixedCounterexample_values : signedMixedCounterexample.permanent=0 ∧
    (signedMixedCounterexample.updateRow 2 (signedMixedCounterexample 1)).permanent=2 ∧
    (signedMixedCounterexample.updateRow 1 (signedMixedCounterexample 2)).permanent=2 := by
  have hp := permanent_three signedMixedCounterexample
  have hu := permanent_three (signedMixedCounterexample.updateRow 2 (signedMixedCounterexample 1))
  have hv := permanent_three (signedMixedCounterexample.updateRow 1 (signedMixedCounterexample 2))
  norm_num [signedMixedCounterexample,Matrix.updateRow,Matrix.of_apply,Function.update,Fin.ext_iff] at hp hu hv
  exact ⟨hp,hu,hv⟩

example : ¬(signedMixedCounterexample.updateRow 2 (signedMixedCounterexample 1)).permanent*
    (signedMixedCounterexample.updateRow 1 (signedMixedCounterexample 2)).permanent ≤
      signedMixedCounterexample.permanent^2 := by
  obtain ⟨hp,hu,hv⟩ := signedMixedCounterexample_values
  rw [hp,hu,hv]
  norm_num

example : signedMixedCounterexample.permanent=0 ∧
    (signedMixedCounterexample.updateRow 2 (signedMixedCounterexample 1)).permanent=2 ∧
    (signedMixedCounterexample.updateRow 1 (signedMixedCounterexample 2)).permanent=2 :=
  signedMixedCounterexample_values

-- Zero rows and columns require neither regularization nor positive permanents.
example : let Z : Board 3 3 := fun _ _ => 0
    (Z.updateRow (Fin.natAdd 1 (1 : Fin 2)) (Z (Fin.natAdd 1 (0 : Fin 2)))).permanent*
      (Z.updateRow (Fin.natAdd 1 (0 : Fin 2)) (Z (Fin.natAdd 1 (1 : Fin 2)))).permanent ≤ Z.permanent^2 := by
  exact permanent_repeated_rows_inequality (n := 1) (A := fun _ _ => 0) (by intros; rfl)

example {n : ℕ} {A : Board (n+2) (n+2)} (hA : ∀ i j, 0 ≤ A i j) :
    (A.updateRow (Fin.natAdd n 1) (A (Fin.natAdd n 0))).permanent*
      (A.updateRow (Fin.natAdd n 0) (A (Fin.natAdd n 1))).permanent ≤ A.permanent^2 :=
  permanent_repeated_rows_inequality hA

#print axioms permanentQuadraticReduce_coeff
#print axioms permanentMixedQuadratic_coeff11
#print axioms capacityReduce_lift_substitution
#print axioms permanentQuadraticReduce_substitution
#print axioms matrixProductPolynomial_repeat_row
#print axioms permanentMixedQuadratic_repeat_row
#print axioms permanentMixedQuadratic_coeff20
#print axioms permanentMixedQuadratic_coeff02
#print axioms permanent_repeated_rows_inequality
end DittertRybin.Tests
