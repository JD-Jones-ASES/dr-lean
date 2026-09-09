import DR.Endpoint.RowCollisionGraph

/-! Exact unordered-pair counting and the quadratic upper bound needed
to localize tripleton moments. The basic quadratic identity permits
arbitrary real coordinates. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Summing the two endpoint stars counts each increasing edge exactly twice. -/
theorem sum_rowPair_incidence {m : ℕ} (f : SampleIndexPair m → ℝ) :
    (∑ i, ∑ e ∈ rowCollisionIncident i, f e) = 2*∑ e, f e := by
  classical
  simp_rw [rowCollisionIncident,Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hi (i : Fin m) : (if e.val.1=i ∨ e.val.2=i then f e else 0) =
      (if e.val.1=i then f e else 0)+(if e.val.2=i then f e else 0) := by
    by_cases h1 : e.val.1=i
    · have h2 : e.val.2 ≠ i := by have := e.property; omega
      simp [h1,h2]
    · by_cases h2 : e.val.2=i <;> simp [h1,h2]
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq]
  simp
  ring

theorem sum_rowPair_incident_product {m : ℕ} (y : Fin m → ℝ) (i : Fin m) :
    (∑ e ∈ rowCollisionIncident i, y e.val.1*y e.val.2) =
      ∑ h ∈ Finset.univ.erase i, y i*y h := by
  classical
  have h := Fintype.sum_equiv (rowIncidentEdgeEquiv i)
    (fun h => y i*y h.val) (fun e => y e.val.val.1*y e.val.val.2) (by
      intro h
      by_cases hh : i < h.val <;> simp [rowIncidentEdgeEquiv,hh,mul_comm])
  have hleft : (∑ h : {h : Fin m // h ≠ i}, y i*y h.val) =
      ∑ h ∈ Finset.univ.erase i, y i*y h :=
    (Finset.sum_subtype (Finset.univ.erase i) (by simp) (fun h => y i*y h)).symm
  have hright : (∑ e : {e : SampleIndexPair m // e.val.1=i ∨ e.val.2=i}, y e.val.val.1*y e.val.val.2) =
      ∑ e ∈ rowCollisionIncident i, y e.val.1*y e.val.2 :=
    (Finset.sum_subtype (rowCollisionIncident i) (by simp [rowCollisionIncident])
      (fun e => y e.val.1*y e.val.2)).symm
  rw [hleft,hright] at h
  exact h.symm

/-- The exact increasing-pair quadratic identity, including signed coordinates. -/
theorem sum_rowPair_products_identity {m : ℕ} (y : Fin m → ℝ) :
    2*(∑ e : SampleIndexPair m, y e.val.1*y e.val.2) =
      (∑ i, y i)^2-∑ i, (y i)^2 := by
  rw [← sum_rowPair_incidence (fun e => y e.val.1*y e.val.2)]
  simp_rw [sum_rowPair_incident_product,Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [pow_two]

theorem sum_rowPair_products_le_half_sq {m : ℕ} (y : Fin m → ℝ) :
    (∑ e : SampleIndexPair m, y e.val.1*y e.val.2) ≤ (1/2)*(∑ i, y i)^2 := by
  have h := sum_rowPair_products_identity y
  have hn : 0 ≤ ∑ i, (y i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  linarith

/-- Increasing pairs outside one specified row. -/
def rowPairsOutside {m : ℕ} (i : Fin m) : Finset (SampleIndexPair m) :=
  Finset.univ.filter (fun e => e.val.1 ≠ i ∧ e.val.2 ≠ i)

/-- The restricted pair moment has the same factor one half, with no
diagonal or reversed-orientation terms. -/
theorem sum_rowPairsOutside_product_le {m : ℕ} (y : Fin m → ℝ) (i : Fin m) :
    (∑ e ∈ rowPairsOutside i, y e.val.1*y e.val.2) ≤
      (1/2)*(∑ h ∈ Finset.univ.erase i, y h)^2 := by
  classical
  let z : Fin m → ℝ := fun h => if h=i then 0 else y h
  have h := sum_rowPair_products_le_half_sq z
  have hs : (∑ h, z h) = ∑ h ∈ Finset.univ.erase i, y h := by
    rw [← Finset.sum_erase_add (Finset.univ) z (Finset.mem_univ i)]
    simp only [z,if_pos rfl,add_zero]
    apply Finset.sum_congr rfl
    intro h hh
    simp [Finset.ne_of_mem_erase hh]
  have he : (∑ e : SampleIndexPair m, z e.val.1*z e.val.2) =
      ∑ e ∈ rowPairsOutside i, y e.val.1*y e.val.2 := by
    rw [rowPairsOutside,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h1 : e.val.1=i <;> by_cases h2 : e.val.2=i <;> simp [z,h1,h2]
  rwa [hs,he] at h

end DittertRybin
