# Zero-rectangle permanent lower bound

For a doubly stochastic n×n matrix A and arbitrary row and column subsets I,J
with |I|+|J|<n and zeros on I×J,
[permanent_lower_bound_of_zero_rectangle](../DR/Square/ZeroRectangle.lean) proves

```
γₙ₋|I| γₙ₋|J| / γₙ₋|I|₋|J| ≤ permanent A,
γₖ = k! / kᵏ.
```

Additional zeros are unrestricted. Empty forbidden axes reduce to the ordinary
van der Waerden bound. The strict cardinality condition preserves a positive
residual degree. The theorem does not classify all equality cases.

## Capacity proof

The argument extends [Gurvits's capacity method](https://arxiv.org/abs/0711.3496).
Set r=|I|, s=|J| and h=n−r−s>0. In the product of the row linear forms, each
monomial has total degree at most n−r in the J variables: rows in I contribute
zero degree there, and each remaining row contributes at most one.
This degree statement also permits signed coefficients and cancellations.

A finite equivalence moves J into the first s coordinates. Each derivative,
followed by setting that coordinate to zero and removing it, decreases the
selected total degree by one. The j-th reduction loses only
`capacityFactor(n−r−j)`. Stability, nonnegative coefficients and homogeneous
degree are retained, including the zero-polynomial cases. The product telescopes:

```
∏ (j=0,…,s−1) capacityFactor(n−r−j) = γₙ₋ᵣ / γₕ.
```

The remaining n−s variables give the ordinary homogeneous capacity factor
γₙ₋ₛ. Initial capacity is one, and the squarefree coefficient is the permanent.
The final reindexing admits arbitrary subsets, without a contiguous-block
hypothesis.

Related zero-rectangle methods use face minimizers, as in Pula–Song–Wanless
(2011), Lemma 1.1, crediting Foregger (1980), and Alexandrov's permanent
inequality as stated by Cheon–Yoon (2006). The primary sources for the capacity and face methods are listed in
[the bibliography](../docs/SOURCES.md); this proof uses the capacity route.

```sh
lake --wfail build Test.ZeroRectangle
```

Tests include sharp small matrices, noncontiguous labels, additional zeros,
empty forbidden axes, the residual γ denominator, signed degree identities,
and the necessity of the zero-rectangle hypothesis.
