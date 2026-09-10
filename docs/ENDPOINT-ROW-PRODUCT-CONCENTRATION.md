# Row concentration from the actual product deficit

Let y be a nonnegative vector whose coordinates sum to its dimension.
If its product is at least 1−b with b<1/4, then

```
sum (y_i−1)² ≤ 8b/(1−b).
```

The product first forces every coordinate into (0,2). Above two, the
proved coordinate envelope is at most 2/e<3/4. The quadratic logarithm
bound follows from `log(sqrt y)≤sqrt y−1` and exact squared inequalities,
without an assumed local expansion. Summing it and retaining the product
deficit denominator yields the dimension-free estimate.

When b≤1/16384 the squared deviation is strictly less than 1/1024.
The actual contender corollary applies this to y_i=m rowSum(P)_i using
the proved full-probability contender relation. No stationarity,
positive-entry assumption, or gauge inequality is used.

## Formal statements

[RowProductConcentration](../DR/Endpoint/RowProductConcentration.lean).
