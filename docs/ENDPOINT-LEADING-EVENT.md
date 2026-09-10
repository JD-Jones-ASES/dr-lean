# Exact endpoint collision correction

`LeadingEvent.endpoint_failure_leading_lower` proves, for every nonnegative
probability board with at least three rows,

```
1 − F_m(P) ≥ 1 − m! e_m(c)
            − choose(m,2) sum_j (c_j^2 − alpha_j^2),
alpha_j = endpointLeadingColumnCost P j.
```

The proof rewrites the endpoint rook identity using one independent
column choice from each normalized row. For positive row masses r_i,
the probability of distinct rows together with a column collision is
m!·∏r_i·(1−p_original). The unordered-pair union bound controls
1−p_original, while the exact leading-kernel identity gives
∑(c_j²−alpha_j²)=2γD with γ=(m−2)!∏r_i and D the collision intensity.
The equality choose(m,2)·2·(m−2)!=m! yields the displayed correction.

A zero row is handled directly: its row product is zero and every actual
column quadratic equals the square of the column mass. No zero row is
normalized into a probability law. Individual zero columns are allowed.
No contender, stationarity, or global gauge conclusion is a premise.

## Formal statements

[LeadingEvent](../DR/Endpoint/LeadingEvent.lean).
