# Zero-rectangle permanent lower bound

The formal theorem is `permanent_lower_bound_of_zero_rectangle` in
`DR/Square/ZeroRectangle.lean`. For a doubly stochastic n×n matrix A,
arbitrary row and column subsets I,J, |I|+|J|<n, and actual zeros on I×J,
it proves

```
gamma_(n-|I|) gamma_(n-|J|) / gamma_(n-|I|-|J|) ≤ per(A),
gamma_k = k! / k^k.
```

Additional zeros are unrestricted. Empty forbidden axes are admitted and
reduce to the ordinary van der Waerden bound. The strict total-cardinality
condition retains a positive residual degree. The theorem does not classify
all minimizers.

## Mathematical sources

The target constant and accepted use in active-cut endpoint ranges appear in
Analytic-Lab P0174 `MINIMUM_DILATION_SQUARE_ENDPOINT.md` and
`ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`. The former attributes its face
minimizer/cofactor route to Pula–Song–Wanless (2011), Lemma 1.1, crediting
Foregger (1980), together with Alexandrov's permanent inequality as stated
by Cheon–Yoon (2006). The formal proof here does not import that cofactor
or face-minimizer result.

Instead it extends the project's self-contained Gurvits capacity proof
(the underlying mathematical source is Gurvits 2008, arXiv:0711.3496v2).
Only the target mathematics was read from the Lab; no peer implementation,
certificate generator, or external theorem-as-axiom was introduced.

Read source hashes:

- `MINIMUM_DILATION_SQUARE_ENDPOINT.md`:
  `e092f6c1eb89e399603b4387fd89b15663a81377995d1f291ea3fda2d77d6d7e`.
- `ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`:
  `4ae2b41d7b6e1969c180501bc336cb567f12fe787ff853bcf465f1d37f32e28e`.

## Exact capacity argument

Set r=|I|, s=|J| and h=n-r-s>0. In the product of the actual row linear
forms, every monomial has total degree at most n-r in the J variables:
the r rows in I contribute degree zero there, and each remaining row
contributes at most one. This support-degree argument permits signed
coefficients and additional cancellations.

An explicit finite equivalence moves J into the first s coordinates.
Each derivative followed by specialization to zero and removal of that
coordinate lowers the selected total-degree bound by one. The actual
univariate slice therefore loses only `capacityFactor(n-r-j)` at the
j-th deletion. Stability, coefficient nonnegativity and homogeneous degree
are inherited by the proved existing reduction lemmas, including their
zero-polynomial branches. The product of these losses telescopes exactly:

```
prod_(j=0..s-1) capacityFactor(n-r-j) = gamma_(n-r)/gamma_h.
```

The remaining n-s variables receive the ordinary homogeneous capacity
bound gamma_(n-s). The initial matrix-product capacity is exactly one,
and its squarefree coefficient is the actual permanent. Independent
physical row and column subset choices are retained by the reindexing
argument; no contiguous-block hypothesis remains in the final theorem.

## Verification

```sh
lake --wfail build Test.ZeroRectangle
```

Persistent tests cover a sharp 3×3 zero in noncontiguous labels, a sharp
4×4 matrix with a nontrivial gamma_2 denominator and a rejected squared-
denominator mutation, an empty forbidden axis, a larger prescribed rectangle
with additional zeros, failure when the zero-rectangle premise is omitted,
the necessity of tracking total selected degree rather than individual
bounds, actual coefficient deletion, signed matrix products, zero polynomial
capacity, and empty-prefix telescoping. The small rational permanent is
checked by `decide +kernel`, with an exact rational-to-real sum/product bridge.
All public proof audits expose only the standard Lean axioms.
