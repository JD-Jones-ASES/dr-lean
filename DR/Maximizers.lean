import DR.Compactness
import DR.Uniform
import Mathlib.Tactic.Ring

/-!
# Closing a strict matrix-averaging argument

When every global maximizer has equal columns, the same fact for the
transposed dimensions gives equal rows. All entries are then equal and
total mass one fixes their value. This route avoids a separate equality
argument for product distributions.
-/

namespace DittertRybin

open scoped BigOperators

theorem IsProbability.transpose {m n : ℕ} {P : Board m n} (hP : IsProbability P) :
    IsProbability P.transpose := by
  refine ⟨fun i j => hP.1 j i, ?_⟩
  change (∑ j, colSum P j) = 1
  exact (totalMass_eq_sum_colSum P).symm.trans hP.2

/-- Constant rows and columns determine the uniform matrix from its total mass. -/
theorem eq_uniformBoard_of_equal_rows_columns {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P)
    (hc : ∀ i a b, P i a = P i b) (hr : ∀ i h j, P i j = P h j) :
    P = uniformBoard m n := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  ext i j
  have he (u : Fin m) (v : Fin n) : P u v = P i j := (hc u v j).trans (hr u i j)
  have hmass := hP.2
  simp only [totalMass, rowSum, he, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hmass
  change P i j = ((m : ℝ) * n)⁻¹
  field_simp
  nlinarith [hmass]

/-- Uniqueness of the global maximizer yields the visible sharp inequality and equality theorem. -/
theorem uniform_maximizer_of_unique_global {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (k : ℕ)
    (hunique : ∀ P : Board m n, IsProbability P →
      (∀ Q : Board m n, IsProbability Q → separationProbability Q k ≤ separationProbability P k) →
      P = uniformBoard m n) : UniformMaximizer m n k := by
  obtain ⟨P, hP, hmax⟩ := exists_separation_maximizer hm hn k
  have heq := hunique P hP hmax
  subst P
  have hu := separationProbability_uniform (k := k) hm hn
  intro Q hQ
  refine ⟨(hmax Q hQ).trans_eq hu, ?_⟩
  constructor
  · intro hQval
    apply hunique Q hQ
    intro R hR
    exact (hmax R hR).trans_eq (hu.trans hQval.symm)
  · intro hQU
    rw [hQU, hu]

/-- Column rigidity in both orientations is enough for the full unique-maximizer statement. -/
theorem uniform_maximizer_of_column_rigidity {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (k : ℕ)
    (hcol : ∀ P : Board m n, IsProbability P →
      (∀ Q : Board m n, IsProbability Q → separationProbability Q k ≤ separationProbability P k) →
      ∀ i a b, P i a = P i b)
    (htranspose : ∀ P : Board n m, IsProbability P →
      (∀ Q : Board n m, IsProbability Q → separationProbability Q k ≤ separationProbability P k) →
      ∀ i a b, P i a = P i b) : UniformMaximizer m n k := by
  apply uniform_maximizer_of_unique_global hm hn k
  intro P hP hmax
  apply eq_uniformBoard_of_equal_rows_columns hm hn hP (hcol P hP hmax)
  have hmaxT : ∀ Q : Board n m, IsProbability Q →
      separationProbability Q k ≤ separationProbability P.transpose k := by
    intro Q hQ
    simpa only [separationProbability_transpose] using hmax Q.transpose hQ.transpose
  have hr := htranspose P.transpose hP.transpose hmaxT
  intro i h j
  exact hr j i h

end DittertRybin
