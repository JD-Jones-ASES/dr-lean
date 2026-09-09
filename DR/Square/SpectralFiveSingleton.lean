import DR.Square.SpectralFiveParameters
import DR.Certificates.SpectralFiveSingletonPositive
import DR.Certificates.SpectralFiveSingletonMonotonicity

/-!
# The actual order-five singleton contradiction

The exact closed-box polynomial certificate is evaluated at the marginal
coordinates of the actual extremal entry. Its endpoint crossing is then
replaced by the actual crossing, and the resulting strict bound contradicts
the genuine four-by-four deletion-minor floor. The independent order-four
theorem is the sole lower-order input.
-/

namespace DittertRybin

open Certificates.SpectralFiveGuards Certificates.SpectralFiveSingleton

theorem five_globalMax_singleton_cut_contradiction (h4 : DittertMaximizer 4)
    (A : Board 5 5) (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A)
    (i j : Fin 5) (hrow : ∀ r, rowSum A i ≤ rowSum A r)
    (hcol : ∀ c, colSum A c ≤ colSum A j)
    (hwW : cutMass A {i} {j}ᶜ + cutMass A {i}ᶜ {j} ≤
      crossingBound (fiveDeficitParameter (dittertConstant 5-A.permanent))) : False := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_,_,_,hd0,hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  let delta := dittertConstant 5-A.permanent
  let t := fiveDeficitParameter delta
  let a := rowSum A i
  let b := colSum A j
  let L := 1-(23/50)*t
  let w := cutMass A {i} {j}ᶜ + cutMass A {i}ᶜ {j}
  have hg : dittertConstant 5 = (24/625:ℝ) := by norm_num [dittertConstant,Nat.factorial]
  have hd1 : delta < 1 := by
    have hdg' := hdg.trans_eq hg
    dsimp [delta]
    linarith
  have ht : 0 ≤ t := fiveDeficitParameter_nonneg _
  have ht1 : t ≤ 9/20 := (fiveDeficitParameter_lt_cap hd0 hdg).le
  obtain ⟨hr,hc⟩ := five_globalMax_marginal_bounds A hA hmass hmax
  obtain ⟨ha1,hb⟩ := five_extremal_marginals_straddle_one A hmass i j hrow hcol
  have hL : 793/1000 ≤ L := by dsimp [L]; linarith
  have hLa : L ≤ a := (hr i).1
  have ha : 793/1000 ≤ a := hL.trans hLa
  have hb1 : b ≤ 49/40 := by
    have hbc : b ≤ 1+t/2 := (hc j).2
    linarith
  have hcolL : ∀ c, L ≤ colSum A c := fun c => (hc c).1
  have hw0 : 0 ≤ w := add_nonneg (cutMass_nonneg hA _ _) (cutMass_nonneg hA _ _)
  have hW : crossingBound t ≤ 13/50 := (crossingBound_lt_thirteen_fiftieths t ht ht1).le
  have hw1 : w ≤ 13/50 := hwW.trans hW
  obtain ⟨x,y,hx,hy,haEq,hbEq⟩ :=
    five_globalMax_singleton_coordinates A hA hmass hmax i j hrow hcol
  change a = 1-(23/50)*t*x at haEq
  change b = 1+(1/2)*t*y at hbEq
  have hgap := singleton_normalized_gap_proved ht ht1 hx.1 hx.2 hy.1 hy.2
  rw [← haEq,← hbEq] at hgap
  have hinv : t^2/(5+t^2) = delta := fiveDeficitParameter_inverse hd0 hd1
  rw [hinv] at hgap
  have hpEq : (24/625:ℝ)-delta = A.permanent := by dsimp [delta]; rw [hg]; ring
  rw [hpEq] at hgap
  have hstrict := singleton_gap_of_crossing_le ha ha1 hb hb1 (by linarith : 0 < L) hLa
    hw0 hwW hW (permanent_nonneg hA) hgap
  have hfloor := five_singleton_actual_permanent_lower h4 A hA hmass hcont i j a b L w
    rfl rfl ha ha1 hb hb1 hL hrow hcolL rfl hw1
  exact (not_lt_of_ge hfloor) hstrict

end DittertRybin
