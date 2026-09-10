import DR.Endpoint.TransitionDeletion
import DR.Endpoint.RowCollisionKernelBounds
import DR.Endpoint.EndpointCoefficient
import DR.Endpoint.EndpointKernelClosure

/-! Full endpoint P2 on the accepted transition interval. All scalar fields
of the actual retained-board kernel are derived from an original contender;
the deleted-row avoidance probability is separately proved positive. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_transition_contender_kernel_posDef {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (a b : Fin n) (hab : a≠b) :
    (averagingKernel (eraseColumns P {a,b}) (m-2)).PosDef := by
  let T := keepColumns P ({a,b}ᶜ)
  let h := totalMass T
  have hm1 : 1≤m := by omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  obtain ⟨hh,hr,hsq,hcap,hseq⟩ := endpoint_transition_deleted_bounds hm hmn hlower hupper hP hcont a b hab
  have hh0 : 0<h := by change 0<totalMass (keepColumns P ({a,b}ᶜ)); linarith
  have hT := keepColumns_nonneg hP.1 ({a,b}ᶜ)
  let X := normalizeRows T
  have hX : ∀ i j,0≤X i j := normalizeRows_nonneg T hT
  have hsX : ∀ i,rowSum X i=1 := normalizeRows_rowSum T (fun i => (hr i).ne')
  have hlow := endpoint_transition_lower_square hm hlower
  obtain ⟨hpdel,ht,hell,hv⟩ := rowCollision_localized_kernel_bounds hm1 X hX hsX
    (4*(m:ℝ)/(n:ℝ)) (by positivity) hcap (endpoint_strip_cap_sq hm1 hlow)
  have hc (j : Fin n) : colSum T j≤2/(n:ℝ) :=
    (colSum_keepColumns_le hP.1 ({a,b}ᶜ) j).trans
      (endpoint_transition_contender_column_cap hm hmn hupper hP hcont j).le
  have hE := endpoint_coefficient_ratio_lower (by omega) T hT hr hh0 hpdel (2/(n:ℝ)) hc hseq
  have hB : EndpointCollisionKernelBounds T h := ⟨hsq.le,ht,hell,hv,hE⟩
  have hpos := averagingKernel_endpoint_posDef (by omega) T hT hr h hh0 hpdel hB
  have he : T=eraseColumns P {a,b} := by
    ext i j
    simp only [T,keepColumns,eraseColumns,Finset.mem_compl]
    by_cases hj : j∈({a,b}:Finset (Fin n)) <;> simp [hj]
  simpa only [he] using hpos

theorem uniform_maximum_transition_endpoint_forward {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2) :
    UniformMaximizer m n m := by
  apply uniform_maximum_endpoint_of_contender_kernel (by omega) (by omega)
  intro P hP hcont
  exact endpoint_transition_contender_kernel_posDef hm hmn hlower hupper hP hcont

theorem uniform_maximum_transition_endpoint_transpose {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2) :
    UniformMaximizer n m m := by
  intro P hP
  have h := uniform_maximum_transition_endpoint_forward hm hmn hlower hupper P.transpose hP.transpose
  have hv : uniformSeparationValue m n m=uniformSeparationValue n m m := by
    unfold uniformSeparationValue
    ring
  rw [separationProbability_transpose,hv] at h
  have heq : P.transpose=uniformBoard m n ↔ P=uniformBoard n m := by
    constructor
    · intro he
      ext i j
      have hij := congrFun (congrFun he j) i
      simpa only [Matrix.transpose_apply,uniformBoard,mul_comm] using hij
    · rintro rfl
      ext i j
      simp only [Matrix.transpose_apply,uniformBoard,mul_comm]
  exact ⟨h.1,h.2.trans heq⟩

/-- The actual sharp endpoint inequality and unique uniform equality on
the transition interval, in both orientations and on the full closed simplex. -/
theorem uniform_maximum_transition_endpoint {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m :=
  ⟨uniform_maximum_transition_endpoint_forward hm hmn hlower hupper,
    uniform_maximum_transition_endpoint_transpose hm hmn hlower hupper⟩

end DittertRybin
