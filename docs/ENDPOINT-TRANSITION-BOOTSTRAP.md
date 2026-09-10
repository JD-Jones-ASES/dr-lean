# Actual transition row-variance bootstrap

For every endpoint contender in the range m≥10^18, m≤n,
m(m−1)≤20n and n≤10000m², the scaled row variance is less than 1/100.
The proof combines relative collision avoidance with the exact row-product
constraint.

Let π=∏_i(m r_i), b=(n)_m/n^m, and p_original be the probability
that independently choosing one column from each normalized original row
gives distinct columns. The contender relation gives

```
1-pi <= (b-p_original)/(1-p_original).
```

The original-row avoidance comparison, `p_original<=b`, and
`1-b>=1/40001` imply the ratio is at most
`40001*(7000000000/m)<1/2000`. All denominators remain positive and the
exponential error follows from `exp(-u)>=1-u`.

The earlier finite-product logarithm bound then proves the actual
scaled-row estimate

```
sum (m*rowSum_i-1)^2 < 1/100.
```

The theorem assumes no positive entries, stationary condition, prescribed
row shape or endpoint gauge. It concerns every full-probability contender
on the closed simplex. Subsequent column deletion must introduce its own
normalized row law and its own avoidance probability.

## Formal statements

[TransitionBootstrap](../DR/Endpoint/TransitionBootstrap.lean).
