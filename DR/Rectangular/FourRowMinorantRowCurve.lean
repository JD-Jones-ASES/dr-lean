import DR.Rectangular.FourRowMinorantStationaryMin
import DR.Rectangular.FourRowMinorantThreeCurve

/-!
# Actual fixed-square row variations

With one coordinate fixed, E3 + gamma E4 is a positive affine function of
the remaining triple product on its fixed-moment circle. The exact rational
rotation therefore supplies both the repeated-entry condition and the
obstruction to a repeated largest entry.
-/

namespace DittertRybin
open scoped BigOperators Topology
open Filter

noncomputable def fourRowMinorantRowObjective (γ : ℝ) (r : Fin 4 → ℝ) : ℝ :=
  fourRowMinorantE3 r + γ*(∏ i,r i)

def IsFourRowMinorantRowMaximum (γ : ℝ) (r : Fin 4 → ℝ) : Prop :=
  ∀ u : Fin 4 → ℝ, (∀ i,0≤u i) → (∑ i,u i)=1 →
    fourRowMinorantSquareSum u=fourRowMinorantSquareSum r →
    (∀ i,0≤fourRowMinorantStationary u i) →
      fourRowMinorantRowObjective γ u ≤ fourRowMinorantRowObjective γ r

noncomputable def fourRowMinorantRowCurve (r : Fin 4 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  let x := threeMomentCurve (fun i : Fin 3 => r i.castSucc) t
  ![x 0,x 1,x 2,r 3]

@[simp] theorem fourRowMinorantRowCurve_zero (r : Fin 4 → ℝ) :
    fourRowMinorantRowCurve r 0=r := by
  funext i
  fin_cases i <;> simp [fourRowMinorantRowCurve,Matrix.cons_val_two,Matrix.cons_val_three]

theorem fourRowMinorantRowCurve_sum (r : Fin 4 → ℝ) (t : ℝ) :
    (∑ i,fourRowMinorantRowCurve r t i)=∑ i,r i := by
  have h := threeMomentCurve_sum (fun i : Fin 3 => r i.castSucc) t
  simp only [Fin.sum_univ_three] at h
  simpa [fourRowMinorantRowCurve,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three] using
    congrArg (fun x => x+r 3) h

theorem fourRowMinorantRowCurve_squareSum (r : Fin 4 → ℝ) (t : ℝ) :
    fourRowMinorantSquareSum (fourRowMinorantRowCurve r t)=fourRowMinorantSquareSum r := by
  have hs := threeMomentCurve_sum (fun i : Fin 3 => r i.castSucc) t
  have hp := threeMomentCurve_pair (fun i : Fin 3 => r i.castSucc) t
  simp only [Fin.sum_univ_three] at hs
  simp only [show (Fin.castSucc (0 : Fin 3) : Fin 4)=0 from rfl,
    show (Fin.castSucc (1 : Fin 3) : Fin 4)=1 from rfl,
    show (Fin.castSucc (2 : Fin 3) : Fin 4)=2 from rfl] at hs hp
  norm_num [fourRowMinorantSquareSum,fourRowMinorantRowCurve,Fin.sum_univ_four,
    Matrix.cons_val_two,Matrix.cons_val_three]
  nlinarith [congrArg (fun x : ℝ => x^2) hs]

theorem fourRowMinorantRowCurve_continuous (r : Fin 4 → ℝ) :
    Continuous (fourRowMinorantRowCurve r) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact threeMomentCoordinate_continuous (r 0) (r 1) (r 2)
  · exact threeMomentCoordinate_continuous (r 1) (r 2) (r 0)
  · exact threeMomentCoordinate_continuous (r 2) (r 0) (r 1)
  · exact continuous_const

theorem fourRowMinorantRowObjective_triple (γ : ℝ) (r : Fin 4 → ℝ) :
    fourRowMinorantRowObjective γ r =
      r 3*(r 0*r 1+r 0*r 2+r 1*r 2)+(1+γ*r 3)*(r 0*r 1*r 2) := by
  rw [fourRowMinorantRowObjective,fourRowMinorantE3_expand]
  simp only [Fin.prod_univ_four]
  ring

theorem fourRowMinorantRowCurve_objective (γ : ℝ) (r : Fin 4 → ℝ) (t : ℝ) :
    fourRowMinorantRowObjective γ (fourRowMinorantRowCurve r t) =
      r 3*(r 0*r 1+r 0*r 2+r 1*r 2)+(1+γ*r 3)*
        (∏ i,threeMomentCurve (fun j : Fin 3 => r j.castSucc) t i) := by
  rw [fourRowMinorantRowObjective_triple]
  simp only [fourRowMinorantRowCurve,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.prod_univ_three]
  rw [threeMomentCurve_pair]
  rfl

/-- Strict row and stationary feasibility is preserved near zero on the exact fixed-q curve. -/
theorem fourRowMinorantRowCurve_eventually_feasible (r : Fin 4 → ℝ)
    (hr : ∀ i,0<r i) (hv : ∀ i,0<fourRowMinorantStationary r i) :
    ∀ᶠ t : ℝ in 𝓝 0, (∀ i,0≤fourRowMinorantRowCurve r t i) ∧
      (∀ i,0≤fourRowMinorantStationary (fourRowMinorantRowCurve r t) i) := by
  let φ : ℝ → ℝ := fun x => 1/4+x*(fourRowMinorantSquareSum r-x)/(2*fourRowMinorantDelta r)
  have hφ : Continuous φ := by fun_prop
  have hstat (t : ℝ) (i : Fin 4) :
      fourRowMinorantStationary (fourRowMinorantRowCurve r t) i=φ (fourRowMinorantRowCurve r t i) := by
    simp only [fourRowMinorantStationary,fourRowMinorantDelta,fourRowMinorantRowCurve_squareSum,φ]
  have hc (i : Fin 4) : Continuous (fun t => fourRowMinorantRowCurve r t i) :=
    (continuous_apply i).comp (fourRowMinorantRowCurve_continuous r)
  have hrow : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,0<fourRowMinorantRowCurve r t i := by
    rw [eventually_all]
    intro i
    exact (isOpen_lt continuous_const (hc i)).mem_nhds (by simpa using hr i)
  have hstationary : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,0<φ (fourRowMinorantRowCurve r t i) := by
    rw [eventually_all]
    intro i
    exact (isOpen_lt continuous_const (hφ.comp (hc i))).mem_nhds
      (by simpa [φ,fourRowMinorantStationary] using hv i)
  filter_upwards [hrow,hstationary] with t ht hvt
  exact ⟨fun i => (ht i).le,fun i => by rw [hstat]; exact (hvt i).le⟩

theorem IsFourRowMinorantRowMaximum.triple_localMax {γ : ℝ} {r : Fin 4 → ℝ}
    (hmax : IsFourRowMinorantRowMaximum γ r) (hγ : 0<γ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) (hv : ∀ i,0<fourRowMinorantStationary r i) :
    IsLocalMax (fun t : ℝ => ∏ i,threeMomentCurve (fun j : Fin 3 => r j.castSucc) t i) 0 := by
  have hf : 0<1+γ*r 3 := add_pos (by norm_num) (mul_pos hγ (hr 3))
  filter_upwards [fourRowMinorantRowCurve_eventually_feasible r hr hv] with t ht
  have h := hmax (fourRowMinorantRowCurve r t) ht.1
    ((fourRowMinorantRowCurve_sum r t).trans hs) (fourRowMinorantRowCurve_squareSum r t) ht.2
  rw [fourRowMinorantRowCurve_objective,fourRowMinorantRowObjective_triple] at h
  have hp : (∏ i,threeMomentCurve (fun j : Fin 3 => r j.castSucc) t i) ≤ r 0*r 1*r 2 := by
    nlinarith
  simpa [Fin.prod_univ_three] using hp

theorem IsFourRowMinorantRowMaximum.triple_repeated {γ : ℝ} {r : Fin 4 → ℝ}
    (hmax : IsFourRowMinorantRowMaximum γ r) (hγ : 0<γ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) (hv : ∀ i,0<fourRowMinorantStationary r i) :
    r 0=r 1 ∨ r 0=r 2 ∨ r 1=r 2 :=
  threeMomentCurve_product_extremum_repeated _ (Or.inr (hmax.triple_localMax hγ hr hs hv))

/-- Breaking a repeated larger coordinate increases the triple product exactly. -/
theorem threeMomentCurve_repeated_product_gain (A B t : ℝ) :
    (∏ i,threeMomentCurve ![A,A,B] t i)-A^2*B =
      4*t^2*(A-B)^3*(t-1)^2*(t+1)^2/(1+3*t^2)^3 := by
  have hd : 1+3*t^2 ≠ 0 := (threeMomentCoordinate_den_pos t).ne'
  norm_num [threeMomentCurve,threeMomentCoordinate,Fin.prod_univ_three,Matrix.cons_val_two]
  field_simp [hd]
  ring

theorem threeMomentCurve_not_localMax_repeated_larger {A B : ℝ} (hAB : B<A) :
    ¬ IsLocalMax (fun t : ℝ => ∏ i,threeMomentCurve ![A,A,B] t i) 0 := by
  intro h
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp h
  let t := min (ε/2) (1/2 : ℝ)
  have ht : 0<t := lt_min (half_pos hε) (by norm_num)
  have htε : t<ε := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t<1 := (min_le_right _ _).trans_lt (by norm_num)
  have hbound := hball (show t ∈ Metric.ball (0:ℝ) ε by
    simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos ht] using htε)
  have hgain := threeMomentCurve_repeated_product_gain A B t
  have hpos : 0<4*t^2*(A-B)^3*(t-1)^2*(t+1)^2/(1+3*t^2)^3 := by
    apply div_pos
    · exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos ht))
        (pow_pos (sub_pos.mpr hAB) 3)) (sq_pos_of_ne_zero (by linarith)))
        (sq_pos_of_pos (by linarith))
    · exact pow_pos (threeMomentCoordinate_den_pos t) 3
  change (∏ i,threeMomentCurve ![A,A,B] t i) ≤ ∏ i,threeMomentCurve ![A,A,B] 0 i at hbound
  rw [threeMomentCurve_zero] at hbound
  have hb : (∏ i : Fin 3, (![A,A,B] : Fin 3 → ℝ) i)=A^2*B := by
    simp only [Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    ring
  rw [hb] at hbound
  nlinarith

end DittertRybin
