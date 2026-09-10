# The actual endpoint coefficient ratio

`DR/Endpoint/EndpointCoefficient.lean` combines the independently proved
sequential elementary-symmetric bound with the all-dimension factorial
guard. For `m>=16`, a nonnegative retained board with positive rows and
mass `h>0`, positive actual row-avoidance probability `p0`, and column cap
`c` satisfying `(m-2)c<=h/2`, it proves

```
4*m^2 <= E / ((product rowSum / h^2) * p0).
```

Here `E` is the actual averaging coefficient `e_(m-2)(colSum P)`.
The row-product scale is bounded by `h^(m-2)/m^m` using the proved
closed-simplex Maclaurin inequality on `normalizeBoard P`; `p0<=1`
follows from the separately normalized independent-row law. The factor
`h^2`, sample-order factorial, and avoidance denominator are all retained.
The elementary lower bound has exactly `(m-2)!` as its ordered-sample
normalization. The only numerical induction is the proved factorial guard
starting at dimension 16.

## Formal statements

[EndpointCoefficient](../DR/Endpoint/EndpointCoefficient.lean).
