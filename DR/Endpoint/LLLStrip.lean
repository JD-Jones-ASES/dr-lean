import DR.Endpoint.LLLStripDeletion
import DR.Endpoint.RowCollisionKernelBounds
import DR.Endpoint.EndpointCoefficient
import DR.Endpoint.ColumnRigidity
import DR.Endpoint.LLLStripDomain

/-! Rybin P2 at K=m on the accepted collision-local endpoint strip.
All assumptions concern the literal integer dimensions. The proof retains
the closed probability simplex, actual deleted-row laws, and unique equality. -/
namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

theorem endpoint_strip_contender_kernel_posDef {m n : ℕ} (hm : 128≤m)
    (hlower : 4096*m^3≤n^2) (hupper : 20*n≤m*(m-1))
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (a b : Fin n) (hab : a≠b) :
    (averagingKernel (eraseColumns P {a,b}) (m-2)).PosDef := by
  let T := keepColumns P ({a,b}ᶜ)
  let h := totalMass T
  have hm1 : 1≤m := by omega
  have hmn : m≤n := by have := endpoint_strip_n_ge hm1 hlower; omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  obtain ⟨hh,hr,hsq,hcap,hseq⟩ := endpoint_strip_deleted_bounds hm hlower hupper hP hcont a b hab
  have hh0 : 0<h := by change 0<totalMass (keepColumns P ({a,b}ᶜ)); linarith
  have hT := keepColumns_nonneg hP.1 ({a,b}ᶜ)
  let X := normalizeRows T
  have hX : ∀ i j,0≤X i j := normalizeRows_nonneg T hT
  have hsX : ∀ i,rowSum X i=1 := normalizeRows_rowSum T (fun i => (hr i).ne')
  obtain ⟨hp,ht,hell,hv⟩ := rowCollision_localized_kernel_bounds hm1 X hX hsX
    (4*(m:ℝ)/(n:ℝ)) (by positivity) hcap (endpoint_strip_cap_sq hm1 hlower)
  have hc (j : Fin n) : colSum T j≤2/(n:ℝ) :=
    (colSum_keepColumns_le hP.1 ({a,b}ᶜ) j).trans
      (endpoint_strip_contender_column_cap hm hmn hupper hP hcont j).le
  have hE := endpoint_coefficient_ratio_lower (by omega) T hT hr hh0 hp (2/(n:ℝ)) hc hseq
  have hB : EndpointCollisionKernelBounds T h :=
    ⟨hsq.le.trans (by norm_num),ht,hell,hv,hE⟩
  have hpos := averagingKernel_endpoint_posDef (by omega) T hT hr h hh0 hp hB
  have he : T=eraseColumns P {a,b} := by
    ext i j
    simp only [T,keepColumns,eraseColumns,Finset.mem_compl]
    by_cases hj : j∈({a,b}:Finset (Fin n)) <;> simp [hj]
  simpa only [he] using hpos

theorem endpoint_strip_maximizer_equal_columns {m n : ℕ} (hm : 128≤m)
    (hlower : 4096*m^3≤n^2) (hupper : 20*n≤m*(m-1))
    (P : Board m n) (hP : IsProbability P)
    (hmax : ∀ Q : Board m n,IsProbability Q→separationProbability Q m≤separationProbability P m) :
    ∀ i a b,P i a=P i b := by
  have hm0 : 0<m := by omega
  have hn0 : 0<n := by have := endpoint_strip_n_ge (by omega) hlower; omega
  have hcont := hmax (uniformBoard m n) (uniformBoard_isProbability hm0 hn0)
  rw [separationProbability_uniform hm0 hn0] at hcont
  intro i a b
  by_cases hab : a=b
  · rw [hab]
  have hkernel := endpoint_strip_contender_kernel_posDef hm hlower hupper hP hcont a b hab
  let x : Fin m → ℝ := fun j => P j a-P j b
  by_contra hi
  have hx : x≠0 := by
    intro hx
    have he := congrFun hx i
    exact hi (sub_eq_zero.mp he)
  have hq : 0<quadraticValue (averagingKernel (eraseColumns P {a,b}) (m-2)) x := by
    simpa [quadraticValue_eq_dotProduct] using hkernel.dotProduct_mulVec_pos hx
  have hmid := hmax (blendColumns P a b (1/2))
    (blendColumns_isProbability hP a b hab (1/2) (by norm_num) (by norm_num))
  have hid := separationProbability_blend_identity_of_two_le (k:=m) P (by omega) a b hab (1/2)
  have hf : 0<(1/2:ℝ)*(1-1/2)*(m.factorial:ℝ) := by
    have hfac : (0:ℝ)<m.factorial := by exact_mod_cast Nat.factorial_pos m
    positivity
  have hpos := mul_pos hf hq
  change 0<(1/2:ℝ)*(1-1/2)*(m.factorial:ℝ)*
    (∑ j,∑ l,(P j a-P j b)*averagingKernel (eraseColumns P {a,b}) (m-2) j l*(P l a-P l b)) at hpos
  linarith only [hid,hmid,hpos]

/-- Full sharp inequality and unique uniform equality on exactly the
accepted endpoint strip, including all zero-entry probability boards. -/
theorem uniform_maximum_endpoint_lll_strip {m n : ℕ} (hm : 128≤m)
    (hlower : 4096*m^3≤n^2) (hupper : 20*n≤m*(m-1)) :
    UniformMaximizer m n m := by
  have hn : 0<n := by have := endpoint_strip_n_ge (by omega) hlower; omega
  apply uniform_maximizer_endpoint_of_column_rigidity (by omega) hn
  exact endpoint_strip_maximizer_equal_columns hm hlower hupper

theorem uniform_maximum_endpoint_lll_strip_transpose {m n : ℕ} (hm : 128≤m)
    (hlower : 4096*m^3≤n^2) (hupper : 20*n≤m*(m-1)) :
    UniformMaximizer n m m := by
  intro P hP
  have h := uniform_maximum_endpoint_lll_strip hm hlower hupper P.transpose hP.transpose
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

/-- The fixed release declaration includes both advertised orientations.
The explicit m≤n premise is retained from the accepted target domain. -/
theorem uniform_maximum_lll_endpoint {m n : ℕ} (hm : 128≤m) (_hmn : m≤n)
    (hlower : 4096*m^3≤n^2) (hupper : 20*n≤m*(m-1)) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m :=
  ⟨uniform_maximum_endpoint_lll_strip hm hlower hupper,
    uniform_maximum_endpoint_lll_strip_transpose hm hlower hupper⟩

end DittertRybin
