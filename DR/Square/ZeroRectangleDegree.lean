import DR.Square.CapacityBound

/-! Total degree in a specified subset of variables. A zero rectangle bounds
this degree in the product of row linear forms, and each actual coefficient-one
deletion lowers the bound by one. Signs of coefficients are unrestricted here. -/
namespace DittertRybin
open scoped BigOperators Pointwise

/-- All monomials have bounded total exponent in the selected variables. -/
def HasSubsetDegreeBound {σ : Type*} (p : MvPolynomial σ ℝ) (S : Finset σ) (d : ℕ) : Prop :=
  ∀ e ∈ p.support, ∑ i ∈ S, e i ≤ d

theorem HasSubsetDegreeBound.mono {σ : Type*} {p : MvPolynomial σ ℝ}
    {S : Finset σ} {d D : ℕ} (h : HasSubsetDegreeBound p S d) (hd : d ≤ D) :
    HasSubsetDegreeBound p S D := fun e he => (h e he).trans hd

theorem hasSubsetDegreeBound_zero {σ : Type*} (S : Finset σ) (d : ℕ) :
    HasSubsetDegreeBound (0 : MvPolynomial σ ℝ) S d := by
  intro e he
  simp at he

theorem hasSubsetDegreeBound_C {σ : Type*} (S : Finset σ) (c : ℝ) :
    HasSubsetDegreeBound (MvPolynomial.C c) S 0 := by
  classical
  intro e he
  have he0 : e=0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp he) (by simp [MvPolynomial.coeff_C,Ne.symm h])
  simp [he0]

theorem hasSubsetDegreeBound_X {σ : Type*} [DecidableEq σ] (S : Finset σ) (j : σ) :
    HasSubsetDegreeBound (MvPolynomial.X j : MvPolynomial σ ℝ) S (if j∈S then 1 else 0) := by
  intro e he
  have heq : e=Finsupp.single j 1 := by
    simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  simp [heq,Finsupp.single_apply]

theorem HasSubsetDegreeBound.add {σ : Type*} [DecidableEq σ]
    {p q : MvPolynomial σ ℝ} {S : Finset σ} {d : ℕ}
    (hp : HasSubsetDegreeBound p S d) (hq : HasSubsetDegreeBound q S d) :
    HasSubsetDegreeBound (p+q) S d := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hp e h
  · exact hq e h

theorem HasSubsetDegreeBound.mul {σ : Type*} [DecidableEq σ]
    {p q : MvPolynomial σ ℝ} {S : Finset σ} {a b : ℕ}
    (hp : HasSubsetDegreeBound p S a) (hq : HasSubsetDegreeBound q S b) :
    HasSubsetDegreeBound (p*q) S (a+b) := by
  intro e he
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q he)
  simp only [Finsupp.add_apply,Finset.sum_add_distrib]
  exact Nat.add_le_add (hp u hu) (hq v hv)

theorem hasSubsetDegreeBound_sum {σ ι : Type*} [DecidableEq σ]
    (S : Finset σ) (T : Finset ι) (p : ι → MvPolynomial σ ℝ) (d : ℕ)
    (h : ∀ i∈T, HasSubsetDegreeBound (p i) S d) :
    HasSubsetDegreeBound (∑ i∈T,p i) S d := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hasSubsetDegreeBound_zero S d
  | @insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem hasSubsetDegreeBound_prod {σ ι : Type*} [DecidableEq σ]
    (S : Finset σ) (T : Finset ι) (p : ι → MvPolynomial σ ℝ) (d : ι → ℕ)
    (h : ∀ i∈T, HasSubsetDegreeBound (p i) S (d i)) :
    HasSubsetDegreeBound (∏ i∈T,p i) S (∑ i∈T,d i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hasSubsetDegreeBound_C S 1
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))

/-- The first s coordinates, allowing empty and oversized prefixes. -/
def prefixVariables (n s : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => j.val<s)

theorem sum_prefixVariables_cons {n s : ℕ} (e : Fin n →₀ ℕ) (a : ℕ) :
    (∑ i ∈ prefixVariables (n+1) (s+1), e.cons a i) =
      a + ∑ i ∈ prefixVariables n s, e i := by
  simp [prefixVariables,Finset.sum_filter,Fin.sum_univ_succ]

/-- Coefficient-one deletion consumes one unit of selected total degree. -/
theorem HasSubsetDegreeBound.capacityReduce {n s d : ℕ}
    {p : MvPolynomial (Fin (n+1)) ℝ}
    (hp : HasSubsetDegreeBound p (prefixVariables (n+1) (s+1)) (d+1)) :
    HasSubsetDegreeBound (capacityReduce p) (prefixVariables n s) d := by
  intro e he
  have hc : e.cons 1 ∈ p.support := by
    rw [MvPolynomial.mem_support_iff,← capacityReduce_coeff]
    exact MvPolynomial.mem_support_iff.mp he
  have h := hp _ hc
  rw [sum_prefixVariables_cons] at h
  omega

/-- The actual row product has restricted total degree at most n minus the
number of forbidden rows. Extra zeros and signed entries are permitted. -/
theorem matrixProductPolynomial_subset_degree {n : ℕ} (A : Board n n)
    (I J : Finset (Fin n)) (hz : ∀ i∈I, ∀ j∈J, A i j=0) :
    HasSubsetDegreeBound (matrixProductPolynomial A) J (n-I.card) := by
  have hrow (i : Fin n) : HasSubsetDegreeBound
      (∑ j, MvPolynomial.C (A i j)*MvPolynomial.X j) J (if i∈I then 0 else 1) := by
    apply hasSubsetDegreeBound_sum
    intro j _
    by_cases hij : i∈I ∧ j∈J
    · simp only [hz i hij.1 j hij.2,MvPolynomial.C_0,zero_mul]
      exact hasSubsetDegreeBound_zero _ _
    · have h := (hasSubsetDegreeBound_C J (A i j)).mul (hasSubsetDegreeBound_X J j)
      apply h.mono
      split_ifs <;> simp_all
  have h := hasSubsetDegreeBound_prod J Finset.univ
    (fun i => ∑ j, MvPolynomial.C (A i j)*MvPolynomial.X j)
    (fun i => if i∈I then 0 else 1) (fun i _ => hrow i)
  have hcount : (∑ i : Fin n, if i∈I then 0 else 1 : ℕ) = n-I.card := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => i∉I), (1:ℕ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i∈I <;> simp [hi]
      _ = n-I.card := by
        have he : Finset.univ.filter (fun i : Fin n => i∉I) = Iᶜ := by ext i; simp
        rw [he]
        simp [Finset.card_compl]
  simpa only [matrixProductPolynomial,hcount] using h

end DittertRybin
