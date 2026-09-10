# Mathematical sources

The [theorem statements](THEOREMS.md) specify the full matrix domains and
equality cases. The square Dittert proof is an alternative proof; the
unrestricted rectangular question remains open. The following sources explain
the mathematical antecedents and the methods adapted in the formalization.

## Dittert and semimatchings

- G.-S. Cheon and Ian M. Wanless,
  [An interpretation of the Dittert conjecture in terms of semi-matchings](https://doi.org/10.1016/j.disc.2007.01.008),
  *Discrete Mathematics* 307 (2007), 2501–2507. This gives the square
  semimatching interpretation. For a probability matrix, the event is
  distinct rows **or** distinct columns in independent draws with replacement.
- Dmitry Rybin, [rectangular P2 question](https://x.com/DmitryRybin1/status/2096907360140697791).
  The post text has not been independently verified. The precise question
  considered here is stated directly in [the definitions](../DR/Semimatching.lean)
  and [Challenge](../Challenge.lean); the attribution is not a proof dependency.
- Pedro Paulo Marques do Nascimento,
  [Dittert conjecture proof project](https://github.com/pedromnasc/dittert-conjecture-proof/tree/894066bbaa715138c98bf3cb7c6fdb4f39a37701),
  with Hongyuan Lu's attributed small-order contribution. This supplies an
  earlier complete square argument. The present proof uses a spectral and
  stationary-cut route, with separate small-order proofs. It imports no code
  or certificates from that project and makes no first-resolution claim.
- Additional square results: [Kafidov, arXiv:2607.19439v1](https://arxiv.org/abs/2607.19439v1)
  and [Li–Xiong–Yang, arXiv:2607.29191v2](https://arxiv.org/abs/2607.29191v2).
  Kafidov's argument is an antecedent for the shared row/column deficit bound.
  These papers' square scope is distinct from the rectangular and
  intermediate-order statements proved here.
- Hwang, [A note on a conjecture on permanents](https://doi.org/10.1016/0024-3795(86)90212-0),
  *Linear Algebra and its Applications* 76 (1986), 31–44. The positive global
  maximizer and supported-cell stationarity antecedents are cited through
  Cheon–Wanless (2012), p. 792 and Lemma 3.6. The original 1986 article is
  not a separately used source. The [positive-maximizer argument](POSITIVE_MAXIMIZERS.md)
  is proved directly by compactness and feasible averaging.

## Permanent bounds and equality

- Leonid Gurvits,
  [Van der Waerden/Schrijver-Valiant like Conjectures and Stable (aka Hyperbolic) Homogeneous Polynomials: One Theorem for all](https://arxiv.org/abs/0711.3496v2),
  *Electronic Journal of Combinatorics* 15 (2008), R66. The stable homogeneous
  polynomial capacity method supplies the permanent lower bound.
- Monique Laurent and Alexander Schrijver,
  [On Leonid Gurvits's proof for permanents](https://ir.cwi.nl/pub/16667),
  *American Mathematical Monthly* 117 (2010), 903–911. Its matrix-specific
  argument supplies the equality method. The [capacity proof](CAPACITY-ROUTE.md)
  includes zero-polynomial and zero-capacity cases explicitly.
- Kyle Pula, Seok-Zun Song and Ian M. Wanless,
  [Minimum permanents on two faces of the polytope of doubly stochastic matrices](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-1022.pdf)
  (2011). Repeated-support face reduction and scalar equalization lead to the
  [two-zero matrix representation](TWO_ZERO_REDUCTION.md) and
  [permanent bounds](TWO_ZERO_PERMANENT.md). The formal proof derives the face
  minimum, cofactor estimates, Alexandrov inequality and feasible averaging;
  additional zero entries are allowed.

## Rectangular endpoint methods

- Gi-Sang Cheon and Ian M. Wanless,
  [Some results towards the Dittert conjecture on permanents](https://users.monash.edu.au/~iwanless/papers/DittertIndecompLAA.pdf),
  *Linear Algebra and its Applications* 436 (2012), 791–801. Lemma 2.3 gives
  the minimum-dilation argument; Lemma 2.2 credits the domination criterion
  to C.-K. Li. The [rectangular transport](../DR/Endpoint/RectangularTransport.lean)
  and [minimum dilation](../DR/Endpoint/MinimumDilation.lean) are proved in Lean.
- Zhekai Pang,
  [Proof of Dittert's conjecture for dimensions n >= 17](https://arxiv.org/abs/2606.01531v1).
  Boundary scaling and the quantitative permanent-ratio method are adapted
  in the rectangular endpoint arguments. Pang's theorem is square-only.
  The [one-zero permanent bound](BOUNDARY_PERMANENT.md) retains the
  Knopp–Sinkhorn attribution through Pang; the original Knopp–Sinkhorn paper
  is not a separately used source.
- Bernhard Haeupler, Barna Saha and Aravind Srinivasan,
  [New Constructive Aspects of the Lovasz Local Lemma](https://arxiv.org/abs/1001.1231v5).
  The conditioning framework is adapted in the collision strips. Finite
  weighted-sum conditioning and the required independence are proved in Lean;
  no resampling algorithm is formalized.

Published results are mathematical sources, not added axioms. Their required
consequences are proved in the repository or supplied by the pinned Mathlib
dependency. The formalization is source-based. No source-author endorsement,
independent human refereeing or broader novelty claim is asserted.
