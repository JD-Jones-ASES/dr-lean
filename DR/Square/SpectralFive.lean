import DR.Square.SpectralFiveSingleton
import DR.Square.OrderFourFinal
import DR.Square.Maximizers

/-!
# Dittert's inequality and unique equality case at order five

An actual nonuniform maximum yields a balanced cut of cardinality one or
two. Both orientations of the size-two cut contradict the proved block
floor. At a singleton cut, transposition selects a minimum row and maximum
column, and the exact singleton certificate contradicts the actual minor
floor. Compactness then covers the entire closed nonnegative simplex.
-/

namespace DittertRybin

open Certificates.SpectralFiveGuards

/-- Every actual global maximum at order five is the uniform matrix. -/
theorem dittert_globalMax_uniform_five (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A) : A = uniformDittertMatrix 5 := by
  by_contra hu
  obtain ⟨I,J,hcard,hlo,hhi,hcross,horder,_,hext⟩ :=
    dittert_globalMax_cut_five A hA hmass hmax hu
  by_cases hsingle : I.card = 1
  · have hJsingle : J.card = 1 := hcard ▸ hsingle
    obtain ⟨i,hI⟩ := Finset.card_eq_one.mp hsingle
    obtain ⟨j,hJ⟩ := Finset.card_eq_one.mp hJsingle
    have horient := hext hsingle i (by simp [hI]) j (by simp [hJ])
    rw [hI,hJ] at hcross
    rcases horient with ⟨hrow,hcol⟩ | ⟨hrow,hcol⟩
    · exact five_globalMax_singleton_cut_contradiction dittert_order_four
        A hA hmass hmax i j hrow hcol hcross
    · have hmassT : totalMass A.transpose = 5 := (totalMass_matrix_transpose A).trans hmass
      apply five_globalMax_singleton_cut_contradiction dittert_order_four
        A.transpose (fun r c => hA c r) hmassT (dittert_globalMax_transpose hmax) j i
        hcol hrow
      simpa only [cutMass_transpose_eq,Matrix.permanent_transpose,add_comm] using hcross
  · have hI : I.card = 2 := by omega
    have hJ : J.card = 2 := hcard ▸ hI
    exact five_globalMax_two_cut_contradiction A hA hmass hmax I J hI hJ horder hcross

/-- Dittert's sharp inequality and unique equality case, without support assumptions. -/
theorem dittert_order_five : DittertMaximizer 5 :=
  dittertMaximizer_of_globalMax_uniform (by norm_num) dittert_globalMax_uniform_five

/-- The equivalent full Rybin square endpoint at order five. -/
theorem uniformMaximizer_five_five_five : UniformMaximizer 5 5 5 :=
  (uniformMaximizer_iff_dittertMaximizer (by decide : 0 < 5)).mpr dittert_order_five

end DittertRybin
