import DR.Endpoint.LongColumnKernelFive
import DR.Endpoint.LongColumnDeletion
import DR.Endpoint.EndpointKernelClosure

/-! Actual deletion and endpoint closure from the two bounds supplied by
the long-column bootstrap. Original and retained row laws stay distinct. -/

namespace DittertRybin
open scoped BigOperators

theorem longColumn_five_contender_kernel_of_caps {m n : ℕ} (hm : 5 ≤ m)
    (hn : 10000*m^2 ≤ n) {P : Board m n} (hP : IsProbability P)
    (hr : (∑ i, ((m : ℝ)*rowSum P i-1)^2) < 1/16)
    (hc : ∀ j, colSum P j < 25/(n : ℝ)) (a b : Fin n) (hab : a ≠ b) :
    (averagingKernel (eraseColumns P {a,b}) (m-2)).PosDef := by
  let T := keepColumns P ({a,b}ᶜ)
  let h := totalMass T
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hnR : (10000 : ℝ)*(m : ℝ)^2 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by nlinarith
  have hmass : h = 1-colSum P a-colSum P b := by
    dsimp only [h,T]
    rw [totalMass_delete_two P a b hab,hP.2]
  have hw0 : 0 ≤ 1-h := by
    rw [hmass]
    linarith [colSum_nonneg hP.1 a,colSum_nonneg hP.1 b]
  have hw : 1-h < 50/(n : ℝ) := by
    rw [hmass]
    have heq : 25/(n : ℝ)+25/(n : ℝ) = 50/(n : ℝ) := by ring
    linarith [hc a,hc b]
  have hscale : (m : ℝ)*(50/(n : ℝ)) ≤ (1/100 : ℝ) := by
    have heq : (m : ℝ)*(50/(n : ℝ)) = 50*(m : ℝ)/(n : ℝ) := by ring
    rw [heq]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hmR,hnR]
  have hmw : (m : ℝ)*(1-h) ≤ (1/100 : ℝ) :=
    ((mul_lt_mul_of_pos_left hw hm0).trans_le hscale).le
  have hh : (3/4 : ℝ) < h := by nlinarith only [hmw,hmR,hw0]
  have hsq := longColumn_kept_row_sq_lt (by omega : 1 ≤ m) hP ({a,b}ᶜ) hmw hr
  have hcap (j : Fin n) : colSum T j ≤ 25/(n : ℝ) :=
    (colSum_keepColumns_le hP.1 ({a,b}ᶜ) j).trans (hc j).le
  have hpos := longColumn_five_retained_kernel_posDef hm hn T
    (keepColumns_nonneg hP.1 ({a,b}ᶜ)) hh hsq hcap
  have he : T = eraseColumns P {a,b} := by
    ext i j
    simp only [T,keepColumns,eraseColumns,Finset.mem_compl]
    by_cases hj : j ∈ ({a,b} : Finset (Fin n)) <;> simp [hj]
  simpa only [he] using hpos

/-- Both actual contender estimates imply the sharp closed-simplex
endpoint inequality with iff uniform equality. -/
theorem uniform_maximum_endpoint_of_longColumn_five_caps {m n : ℕ} (hm : 5 ≤ m)
    (hn : 10000*m^2 ≤ n)
    (hbound : ∀ P : Board m n, IsProbability P →
      uniformSeparationValue m n m ≤ separationProbability P m →
      (∑ i, ((m : ℝ)*rowSum P i-1)^2) < 1/16 ∧
      (∀ j, colSum P j < 25/(n : ℝ))) :
    UniformMaximizer m n m := by
  have hn0 : 0 < n := by
    have hp : 0 < m^2 := pow_pos (by omega : 0 < m) 2
    omega
  apply uniform_maximum_endpoint_of_contender_kernel (by omega) hn0
  intro P hP hcont
  obtain ⟨hr,hc⟩ := hbound P hP hcont
  exact longColumn_five_contender_kernel_of_caps hm hn hP hr hc

end DittertRybin
