# Shared marginal control at rectangular endpoint contenders

The proof in [MarginalDiscrepancy.lean](../DR/Endpoint/MarginalDiscrepancy.lean)
works with every nonnegative probability board P whose m-sample separation
probability is at least the uniform value. It assumes 3 ≤ m ≤ n and
b = (n)_m/n^m ≤ 1/4. Individual cells may vanish.

Write a = m!/m^m, R = m^m product of the row sums, S for the normalized
column elementary sum S=m! e_m(c)/b, where c is the vector of column sums,
and δ = b − m^m rookSum(P,m). The
contender identity gives

    (1−R) + (b/a)(1−S) ≤ δ,  0 ≤ δ ≤ b.

For every row subset I and column subset J, let x and y be the absolute
differences between their marginal masses and |I|/m, |J|/n. The joint bound is

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

The binary-entropy method follows the marginal comparison used in
[Pang’s square boundary argument](https://arxiv.org/abs/2606.01531v1).
Here the row and column estimates are coupled by the rectangular rook
deficit. The resulting bound supplies the marginal error term in
[balanced boundary scaling](ENDPOINT-BOUNDARY-SCALING.md).

## Formal statements

[MarginalDiscrepancy](../DR/Endpoint/MarginalDiscrepancy.lean).
