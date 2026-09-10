# Shared marginal control at rectangular endpoint contenders

The proof in [MarginalDiscrepancy.lean](../DR/Endpoint/MarginalDiscrepancy.lean)
works with every nonnegative probability board P whose m-sample separation
probability is at least the uniform value. It assumes 3 ≤ m ≤ n and
b = (n)_m/n^m ≤ 1/4. Individual cells may vanish.

Write a = m!/m^m, R = m^m product of the row sums, S for the normalized
column elementary sum, and δ = b − m^m rookSum(P,m). The already proved
contender identity gives

    (1−R) + (b/a)(1−S) ≤ δ,  0 ≤ δ ≤ b.

For every row subset I and column subset J, let x and y be the absolute
differences between their marginal masses and |I|/m, |J|/n. The new theorem is

    (x+y)^2 ≤ [2/(3m)] [1+(n−1)a/b] δ.

The row estimate reuses the generic binary relative entropy and grouped
logarithmic AM–GM proof in
[the square marginal module](../DR/Square/MarginalDiscrepancy.lean).
Scaling its input by m gives x² ≤ 2(1−R)/(3m). For columns, closed-simplex
Maclaurin stability gives a variance bound. A sign vector taking values ±1,
together with the zero sum of the centered marginal, proves the exact
factor-four inequality y² ≤ n Var(c)/4. Consequently
y² ≤ 2(n−1)(1−S)/(3m). A weighted two-coordinate Cauchy inequality uses
the shared deficit budget once.

Empty and full subsets are included. The elementary step retains a zero
coordinate and deficit 1/4; positivity of the row sums is derived from the
contender condition. The variance lemma itself allows signed vectors of
mass one. No cut criterion or matrix domination is assumed here.

The mathematical derivation is the rectangular adaptation recorded in
Analytic-Lab P0174, PANG_RECTANGULAR_ENDPOINT.md, with Pang's binary estimate
as the attributed antecedent. This is a formalization of that accepted
argument, not a claim of a new unrestricted P2 theorem.

Replay:

```sh
lake --wfail build +Test.EndpointMarginalDiscrepancy
```

The persistent tests include a sharp boundary variance example, signed
mass-one input, rejected normalization and constant weakenings, a genuine
zero-column elementary vector at deficit 1/4, and the weighted shared budget.
The six principal APIs use only propext, Classical.choice and Quot.sound.
