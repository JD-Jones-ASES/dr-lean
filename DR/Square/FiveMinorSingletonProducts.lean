import DR.Square.FiveMinorGeometry
import DR.Square.FiveMinorFactors

/-! Actual row and column product factors for the distinguished singleton deletion. -/

namespace DittertRybin
open scoped BigOperators

theorem five_singleton_actual_products {n : ℕ} (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (i j : Fin n) (a b L w : ℝ)
    (haEq : rowSum A i = a) (hbEq : colSum A j = b)
    (ha : 793/1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49/40)
    (hL : 793/1000 ≤ L) (hrow : ∀ r, a ≤ rowSum A r) (hcol : ∀ c, L ≤ colSum A c)
    (hw : cutMass A {i} {j}ᶜ + cutMass A {i}ᶜ {j} = w) (hw1 : w ≤ 13/50) :
    ((∏ r, rowSum A r) * fiveSingletonRowFactor a b w ≤
      ∏ r : ↥({i}ᶜ : Finset (Fin n)), ∑ c ∈ ({j}ᶜ : Finset (Fin n)), A r c) ∧
    ((∏ c, colSum A c) * fiveSingletonColFactor a b L w ≤
      ∏ c : ↥({j}ᶜ : Finset (Fin n)), ∑ r ∈ ({i}ᶜ : Finset (Fin n)), A r c) := by
  have hrI : (∑ r ∈ ({i}:Finset (Fin n)), rowSum A r) = 1-(1-a) := by simp [haEq]
  have hcJ : (∑ c ∈ ({j}:Finset (Fin n)), colSum A c) = 1+(b-1) := by simp [hbEq]
  obtain ⟨he,hf,_,_⟩ := cut_block_mass_identities A {i} {j} 1 (1-a) (b-1) w
    (totalMass A) rfl hrI hcJ hw
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hL0 : 0 < L := by linarith
  have hRcomp : (∏ r ∈ (({i}ᶜ : Finset (Fin n))ᶜ), rowSum A r) ≤ a := by
    simp [haEq]
  have hCcomp : (∏ c ∈ (({j}ᶜ : Finset (Fin n))ᶜ), colSum A c) ≤ b := by
    simp [hbEq]
  have hR := cut_row_product_lower_of_complement_upper A hA {i}ᶜ {j}ᶜ a a ha0 ha0
    (fun r _ => hrow r) hRcomp (by rw [compl_compl,hf]; linarith)
  have hC := cut_col_product_lower_of_complement_upper A hA {i}ᶜ {j}ᶜ L b hL0 hb0
    (fun c _ => hcol c) hCcomp (by rw [compl_compl,he]; linarith)
  rw [compl_compl,hf] at hR
  rw [compl_compl,he] at hC
  have hRf : (1-((w+(1-a)+(b-1))/2)/a)/a = fiveSingletonRowFactor a b w := by
    unfold fiveSingletonRowFactor
    field_simp [ha0.ne']
    ring
  have hCf : (1-((w-(1-a)-(b-1))/2)/L)/b = fiveSingletonColFactor a b L w := by
    unfold fiveSingletonColFactor
    field_simp [hL0.ne',hb0.ne']
    ring
  rw [hRf] at hR
  rw [hCf] at hC
  exact ⟨hR,hC⟩

end DittertRybin
