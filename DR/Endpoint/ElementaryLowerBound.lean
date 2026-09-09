import DR.Rook
import Mathlib.Data.Fin.Tuple.Embedding

/-! A lower bound for the actual elementary symmetric coefficient, obtained
by extending distinct ordered samples. Zero coordinates and sample order zero
are retained. No collision-avoidance estimate is assumed. -/
namespace DittertRybin
open scoped BigOperators
noncomputable section

/-- Remove the first label of an injection, retaining it outside the tail range. -/
def distinctSampleSuccEquiv (d k : ℕ) :
    (Fin (k+1) ↪ Fin d) ≃ (Σ e : Fin k ↪ Fin d, {a : Fin d // a ∉ Set.range e}) where
  toFun e := ⟨Fin.Embedding.tail e, e 0, by
    rintro ⟨i,hi⟩
    have he : e i.succ = e 0 := hi
    have hh := e.injective he
    exact Fin.succ_ne_zero i hh⟩
  invFun q := Fin.Embedding.cons q.1 q.2.property
  left_inv e := by
    apply Function.Embedding.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv q := by
    rcases q with ⟨e,a,ha⟩
    rfl

/-- The unused-label mass is exactly the total minus the used-label mass. -/
theorem sum_outside_embedding {d k : ℕ} (x : Fin d → ℝ) (e : Fin k ↪ Fin d) :
    (∑ a : {a : Fin d // a ∉ Set.range e}, x a) = (∑ a, x a)-(∑ i,x (e i)) := by
  classical
  let : Fintype {a : Fin d // a ∈ Set.range e} := Subtype.fintype _
  have hs := Fintype.sum_subtype_add_sum_subtype (p := fun a : Fin d => a ∈ Set.range e) x
  have he : (∑ a : {a : Fin d // a ∈ Set.range e}, x a) = ∑ i,x (e i) := by
    exact ((Equiv.ofInjective e e.injective).sum_comp (fun a => x a)).symm
  have hs' : (∑ a : {a : Fin d // a ∈ Set.range e}, x a) +
      (∑ a : {a : Fin d // a ∉ Set.range e}, x a) = ∑ a,x a := hs
  rw [he] at hs'
  linarith

/-- Exact signed recurrence; the factor k! is accounted for by ordered injections. -/
theorem sum_embeddings_successor {d k : ℕ} (x : Fin d → ℝ) :
    (∑ e : Fin (k+1) ↪ Fin d, ∏ i,x (e i)) =
      ∑ e : Fin k ↪ Fin d, (∏ i,x (e i))*((∑ a,x a)-(∑ i,x (e i))) := by
  classical
  rw [← (distinctSampleSuccEquiv d k).symm.sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  have hp (a : {a : Fin d // a ∉ Set.range e}) :
      (∏ i, x ((distinctSampleSuccEquiv d k).symm ⟨e,a⟩ i)) = x a*(∏ i,x (e i)) := by
    rw [Fin.prod_univ_succ]
    rfl
  simp only [hp, ← Finset.sum_mul, sum_outside_embedding]
  ring

/-- Every admitted distinct prefix leaves at least b mass for its next label. -/
theorem sum_embeddings_step_lower {d k : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i,0≤x i) (h c b : ℝ) (hsum : ∑ i,x i=h)
    (hcap : ∀ i,x i≤c) (hk : (k:ℝ)*c≤h-b) :
    b*(∑ e : Fin k ↪ Fin d, ∏ i,x (e i)) ≤
      ∑ e : Fin (k+1) ↪ Fin d, ∏ i,x (e i) := by
  rw [sum_embeddings_successor,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hu : (∑ i,x (e i))≤(k:ℝ)*c := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hcap (e i))
  have hp : 0≤∏ i,x (e i) := Finset.prod_nonneg (fun i _ => hx (e i))
  rw [hsum]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (by linarith : b≤h-∑ i,x (e i)) hp

/-- A full finite-domain coefficient bound, including zero coordinates and k=0. -/
theorem elementarySymmetric_lower_of_cap {d k : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i,0≤x i) (h c : ℝ) (hh : 0<h) (hsum : ∑ i,x i=h)
    (hcap : ∀ i,x i≤c) (hk : (k:ℝ)*c≤h/2) :
    (h/2)^k≤(k.factorial:ℝ)*elementarySymmetric x k := by
  classical
  have hspos : 0<∑ i,x i := by rw [hsum]; exact hh
  have hc : 0≤c := by
    by_contra hc
    have hn : (∑ i,x i)≤0 := Finset.sum_nonpos
      (fun i _ => (hcap i).trans (le_of_lt (lt_of_not_ge hc)))
    linarith
  have hb : 0≤h/2 := by positivity
  have H : ∀ j : ℕ,j≤k→(h/2)^j≤∑ e : Fin j ↪ Fin d,∏ i,x (e i) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      have hjc : (j:ℝ)*c≤h-h/2 := by
        have hle : (j:ℝ)≤k := Nat.cast_le.mpr (by omega)
        have hm := mul_le_mul_of_nonneg_right hle hc
        linarith
      calc
        (h/2)^(j+1)=(h/2)*(h/2)^j := by rw [pow_succ]; ring
        _≤(h/2)*(∑ e : Fin j ↪ Fin d,∏ i,x (e i)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hb
        _≤_ := sum_embeddings_step_lower x hx h c (h/2) hsum hcap hjc
  simpa only [sum_embeddings_eq_factorial_elementary] using H k le_rfl

end
end DittertRybin
