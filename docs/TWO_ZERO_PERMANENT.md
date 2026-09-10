# Two independent zeros: actual permanent floors

For every doubly stochastic matrix D of order N at least 27 with two zero
entries in distinct rows and columns, the formal theorem is

    permanent(D) > mu(N) * (1 + 1/(4*(N-2)^2)),

where mu(N) is the proved sharp one-zero permanent floor. Arbitrary additional
zeros are permitted. The strict finite references needed for orders 22 through
26 are also proved using the exact rational cubic brackets.

The proof chain is unconditional: a compact full-face minimum, a least-norm
choice, the supported-cofactor and strict Hall arguments, actual Alexandrov
averaging, the reduced matrix representation, its exact signed permanent
calculation, and the scalar polynomial/logarithmic bounds. None of the face
shape, permanent floors, or desired semimatching conclusions is assumed by
the public theorems.

`twoZeroReducedPermanent_representative` exposes the intermediate actual
matrix-to-scalar reduction on every order n+2 with n at least two. This is the
interface used to discharge the near-endpoint permanent premise.

The mathematical face and scalar model follows
[Pula, Song and Wanless (2011)](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-1022.pdf)
and the Lab's audited `TWO_ZERO_PERMANENT_GAP.md` derivation. The formal support
and averaging arguments are internal proofs using the previously verified
stable-polynomial prerequisites.

Run `lake build +Test.TwoZeroPermanent`. The examples check the first tail
order with an actual identity matrix, both finite endpoint orders, the exact
closed-simplex representative scope, and the distinct-row requirement.
