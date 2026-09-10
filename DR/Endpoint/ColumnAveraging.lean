import DR.Endpoint.ColumnDeletionLower
import DR.Compactness

/-! Finite midpoint averaging on a capped closed simplex. A minimum-norm
tie breaker proves the uniform comparison even when every objective gain
is only non-strict. This is the finite averaging form of Schur comparison. -/
namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointColumnMidpoint {d : ℕ} (x : Fin d → ℝ) (a b : Fin d) : Fin d → ℝ :=
  fun i => if i=a then (x a+x b)/2 else if i=b then (x a+x b)/2 else x i

theorem endpointColumnMidpoint_correction {d : ℕ} (x : Fin d → ℝ)
    (a b : Fin d) (hab : a≠b) (i : Fin d) :
    endpointColumnMidpoint x a b i=x i+
      (if i=a then (x b-x a)/2 else 0)+(if i=b then (x a-x b)/2 else 0) := by
  by_cases ha : i=a <;> by_cases hb : i=b <;> simp_all [endpointColumnMidpoint] <;> ring

theorem endpointColumnMidpoint_sum {d : ℕ} (x : Fin d → ℝ)
    (a b : Fin d) (hab : a≠b) : (∑ i,endpointColumnMidpoint x a b i)=∑ i,x i := by
  simp only [endpointColumnMidpoint_correction x a b hab,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

theorem endpointColumnMidpoint_square {d : ℕ} (x : Fin d → ℝ)
    (a b : Fin d) (hab : a≠b) :
    (∑ i,(endpointColumnMidpoint x a b i)^2)=(∑ i,(x i)^2)-(x a-x b)^2/2 := by
  have he (i : Fin d) : (endpointColumnMidpoint x a b i)^2=(x i)^2+
      (if i=a then ((x a+x b)/2)^2-(x a)^2 else 0)+
      (if i=b then ((x a+x b)/2)^2-(x b)^2 else 0) := by
    by_cases ha : i=a <;> by_cases hb : i=b <;> simp_all [endpointColumnMidpoint]
  simp only [he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

def endpointCappedSimplex (d : ℕ) (C : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i,x i∈Set.Icc 0 C) ∧ ∑ i,x i=1}

theorem endpointColumnMidpoint_mem {d : ℕ} {C : ℝ} {x : Fin d → ℝ}
    (hx : x∈endpointCappedSimplex d C) (a b : Fin d) (hab : a≠b) :
    endpointColumnMidpoint x a b∈endpointCappedSimplex d C := by
  constructor
  · intro i
    dsimp [endpointColumnMidpoint]
    split_ifs
    · constructor <;> linarith [(hx.1 a).1,(hx.1 b).1,(hx.1 a).2,(hx.1 b).2]
    · constructor <;> linarith [(hx.1 a).1,(hx.1 b).1,(hx.1 a).2,(hx.1 b).2]
    · exact hx.1 i
  · rw [endpointColumnMidpoint_sum x a b hab]
    exact hx.2

theorem isCompact_endpointCappedSimplex (d : ℕ) (C : ℝ) :
    IsCompact (endpointCappedSimplex d C) := by
  have hb : IsCompact {x : Fin d → ℝ | ∀ i,x i∈Set.Icc 0 C} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  exact hb.inter_right (isClosed_eq (by fun_prop) continuous_const)

/-- A genuine compact minimum plus a minimum-norm tie breaker yields uniformity.
Only the actual pair-averaging inequality is assumed. -/
theorem endpoint_midpoint_uniform_comparison {d : ℕ} (hd : 0<d) (C : ℝ)
    (F : (Fin d → ℝ) → ℝ) (hF : Continuous F)
    (hmid : ∀ x∈endpointCappedSimplex d C,∀ a b : Fin d,a≠b→
      F (endpointColumnMidpoint x a b)≤F x)
    (x : Fin d → ℝ) (hx : x∈endpointCappedSimplex d C) :
    F (fun _ => 1/(d:ℝ))≤F x := by
  let K := endpointCappedSimplex d C
  have hK : IsCompact K := isCompact_endpointCappedSimplex d C
  obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn ⟨x,hx⟩ hF.continuousOn
  let L := K∩{z | F z=F y}
  have hL : IsCompact L := hK.inter_right (isClosed_eq hF continuous_const)
  have hnorm : Continuous (fun z : Fin d → ℝ => ∑ i,(z i)^2) := by fun_prop
  obtain ⟨z,hz,hsmall⟩ := hL.exists_isMinOn ⟨y,hy,rfl⟩ hnorm.continuousOn
  have hequal (a b : Fin d) : z a=z b := by
    by_contra hne
    have hab : a≠b := by intro h; exact hne (congrArg z h)
    have hw := endpointColumnMidpoint_mem hz.1 a b hab
    have hle := hmid z hz.1 a b hab
    have hge := hmin hw
    change F y≤F (endpointColumnMidpoint z a b) at hge
    have hval : F (endpointColumnMidpoint z a b)=F y := by
      have hzval : F z=F y := hz.2
      linarith
    have hsq := hsmall (show endpointColumnMidpoint z a b∈L from ⟨hw,hval⟩)
    change (∑ i,(z i)^2)≤∑ i,(endpointColumnMidpoint z a b i)^2 at hsq
    rw [endpointColumnMidpoint_square z a b hab] at hsq
    have hp : 0<(z a-z b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    linarith
  have hzuniform : z=fun _ => 1/(d:ℝ) := by
    funext i
    have hs := hz.1.2
    have he : (∑ j,z j)=(d:ℝ)*z i := by
      calc
        _=∑ _j : Fin d,z i := Finset.sum_congr rfl (fun j _ => hequal j i)
        _=_ := by simp
    rw [he] at hs
    have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
    apply (eq_div_iff hdR).mpr
    nlinarith only [hs]
  have hzval : F z=F y := hz.2
  rw [hzuniform] at hzval
  exact hzval.trans_le (hmin hx)

end DittertRybin
