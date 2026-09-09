import DR.Certificates.FiniteK4QuinticLocal
import DR.Rectangular.FourRowFiniteDataRows
import DR.Rectangular.FourRowFiniteFamilyPolynomial

/-! Exact sparse row interpretation and the84-equation four-row restriction.
The literal finite equations are connected to the separately verified
four-row numerator families; padding has coefficient zero. -/
namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem finiteK4QuinticRowTerms_padding : ∀ a : Fin 91,
    List.ofFn (finiteK4QuinticTerm a) = finiteK4QuinticRows.get a ++
      List.replicate (10-(finiteK4QuinticRows.get a).length) (0,0) := by
  intro a
  fin_cases a <;> decide +kernel

theorem finiteK4QuinticRowValue_list (coeff : Fin 407 → ℝ) (a : Fin 91) :
    finiteK4QuinticRowValue coeff a =
      ((finiteK4QuinticRows.get a).map (fun t => (t.2 : ℝ)*coeff t.1)).sum := by
  unfold finiteK4QuinticRowValue
  rw [←List.sum_ofFn]
  have he : List.ofFn (fun k : Fin 10 => ((finiteK4QuinticTerm a k).2 : ℝ)*coeff (finiteK4QuinticTerm a k).1) =
      (List.ofFn (finiteK4QuinticTerm a)).map (fun t => (t.2 : ℝ)*coeff t.1) := by
    simp only [List.map_ofFn,Function.comp_def]
  rw [he,finiteK4QuinticRowTerms_padding,List.map_append,List.sum_append]
  simp

theorem finiteK4QuinticFourRowRows : ∀ a : Fin 84,
    finiteK4QuinticRows.get (finiteK4QuinticFourRowEquations.get a) =
      ((fourRowFiniteCoefficientRows a).terms.map (fun t => (finiteK4FourRowRoleIndices.get t.1,t.2))) ∧
    finiteK4QuinticMultiplicity.get (finiteK4QuinticFourRowEquations.get a) =
      (fourRowFiniteCoefficientRows a).multiplicity ∧
    finiteK4QuinticSuccesses.get (finiteK4QuinticFourRowEquations.get a) =
      (fourRowFiniteCoefficientRows a).successes := by
  intro a
  fin_cases a <;> decide +kernel

theorem finiteK4QuinticFourRowEquation_coverage : ∀ r : Fin 51, ∀ c : Fin 52,
    ∃ a : Fin 84, finiteK4QuinticFourRowEquations.get a = finiteK4QuinticEquation r.castSucc c := by
  intro r
  fin_cases r <;> decide +kernel

def FiniteK4FourRowCoefficientEquations (alpha : ℝ) (coeff : Fin 407 → ℝ) : Prop :=
  ∀ a : Fin 84, finiteK4QuinticRowValue coeff (finiteK4QuinticFourRowEquations.get a) =
    (finiteK4QuinticMultiplicity.get (finiteK4QuinticFourRowEquations.get a) : ℝ)*alpha -
      (finiteK4QuinticSuccesses.get (finiteK4QuinticFourRowEquations.get a) : ℝ)

theorem FiniteK4FourRowCoefficientEquations.physical_row {n : ℕ} {alpha : ℝ}
    {coeff : Fin 407 → ℝ} (h : FiniteK4FourRowCoefficientEquations alpha coeff)
    (s : Fin 5 → Fin 4 × Fin n) :
    finiteK4QuinticRowValue coeff (finiteK4QuinticEquation
      (fiveTuplePatternIndex (fun i => (s i).1)) (fiveTuplePatternIndex (fun i => (s i).2))) =
    (finiteK4QuinticMultiplicity.get (finiteK4QuinticEquation
      (fiveTuplePatternIndex (fun i => (s i).1)) (fiveTuplePatternIndex (fun i => (s i).2))) : ℝ)*alpha -
    (finiteK4QuinticSuccesses.get (finiteK4QuinticEquation
      (fiveTuplePatternIndex (fun i => (s i).1)) (fiveTuplePatternIndex (fun i => (s i).2))) : ℝ) := by
  have hr : ¬Function.Injective (fun i => (s i).1) := by
    intro hi
    have hc := Fintype.card_le_of_injective _ hi
    norm_num at hc
  let r : Fin 51 := ⟨(fiveTuplePatternIndex (fun i => (s i).1)).val,
    fiveTuplePatternIndex_lt_fiftyOne _ hr⟩
  obtain ⟨a,ha⟩ := finiteK4QuinticFourRowEquation_coverage r (fiveTuplePatternIndex (fun i => (s i).2))
  have he := h a
  rw [ha] at he
  exact he

/-- The universal407-entry coefficient function restricts to the actual391 family roles. -/
def fourRowFiniteUniversalCoefficient (h : Fin 391 → Fin 5 → ℚ) (u : ℝ) (k : Fin 407) : ℝ :=
  fourRowFiniteNumeratorValue h (fourRowFiniteRoleLookup (finiteK4RoleKeys.get k)) u/u

theorem fourRowFiniteUniversalCoefficient_key (h : Fin 391 → Fin 5 → ℚ) (u : ℝ) (k : Fin 391) :
    fourRowFiniteUniversalCoefficient h u (finiteK4FourRowRoleIndices.get k) =
      fourRowFiniteNumeratorValue h k u/u := by
  simp only [fourRowFiniteUniversalCoefficient,fourRowFiniteRoleLookup_key]

theorem fourRowFiniteUniversalCoefficient_equations (a : ℕ) (h : Fin 391 → Fin 5 → ℚ)
    (hv : ∀ e : Fin 84, (fourRowFiniteCoefficientRows e).Valid a h)
    (u : ℝ) (hu : u ≠ 0) :
    FiniteK4FourRowCoefficientEquations
      (1-87/(16*a)*u+319/(32*a^2)*u^2-87/(16*a^3)*u^3)
      (fourRowFiniteUniversalCoefficient h u) := by
  intro e
  obtain ⟨hr,hm,hs⟩ := finiteK4QuinticFourRowRows e
  rw [finiteK4QuinticRowValue_list,hr,hm,hs,List.map_map]
  have he := FourRowFiniteCoefficientRow.Valid.eval (fourRowFiniteCoefficientRows e) a h (hv e) u
  have hscl :
      (((fourRowFiniteCoefficientRows e).terms.map fun t =>
        (t.2 : ℝ)*fourRowFiniteUniversalCoefficient h u (finiteK4FourRowRoleIndices.get t.1))).sum =
      (((fourRowFiniteCoefficientRows e).terms.map fun t =>
        (t.2 : ℝ)*fourRowFiniteNumeratorValue h t.1 u)).sum/u := by
    simp only [fourRowFiniteUniversalCoefficient_key,←mul_div_assoc]
    generalize (fourRowFiniteCoefficientRows e).terms = ts
    induction ts with
    | nil => simp
    | cons t ts ih => simp only [List.map_cons,List.sum_cons,ih,add_div]
  change (((fourRowFiniteCoefficientRows e).terms.map fun t =>
    (t.2 : ℝ)*fourRowFiniteUniversalCoefficient h u (finiteK4FourRowRoleIndices.get t.1))).sum = _
  rw [hscl,he,mul_div_cancel_left₀ _ hu]

end
end DittertRybin.Certificates
