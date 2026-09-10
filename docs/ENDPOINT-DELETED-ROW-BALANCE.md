# Actual row balance after column deletion

Suppose a probability board has scaled-row squared deviation below
1/1024. Delete nonnegative row masses τ_i≤r_i with total w=∑τ_i
and m w≤1/16. The retained normalized row masses
s_i=(r_i−τ_i)/(1−w) satisfy ∑(1−m s_i)²<1/81, which is below
the kernel criterion’s threshold 1/9. Individual deletion masses may be zero.

The proof keeps the exact centered deletion vector `m*tau-w`. Its squared
norm is at most `m^2*w^2`. The elementary squared triangle bound and
`1-w>=15/16` yield the estimate directly. A coordinate consequence gives
every retained normalized row greater than `2/(3m)`.

For actual column deletion, take τ_i to be the mass removed from row i.
The sum of the retained entries is 1−w, so normalizing the retained board
gives exactly the row vector s above. The argument establishes positive
retained rows without assuming them beforehand.

## Formal statements

[DeletedRowBalance](../DR/Endpoint/DeletedRowBalance.lean).
