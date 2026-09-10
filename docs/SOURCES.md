# Mathematical sources and provenance

The mathematical statement and the proof are separate provenance questions.

- **Rybin's rectangular formulation:** Dmitry Rybin's
  [P2 post](https://x.com/DmitryRybin1/status/2096907360140697791), supplied
  by JD as the only statement location he found. Direct retrieval on
  2026-09-09 returned a cache miss. The statement used here is fixed explicitly
  in the Lean definitions and Lab notes; independent retrieval of the post
  text is not claimed, and no immediate paper source is inferred.
- **Published square semimatching antecedent:** G.-S. Cheon and I. M. Wanless,
  [An interpretation of the Dittert conjecture in terms of semi-matchings](https://doi.org/10.1016/j.disc.2007.01.008),
  Discrete Mathematics 307 (2007), 2501–2507. Its coefficient-one objective
  matches square P2. It is not the same intermediate-order normalization
  as the older Cheon–Hwang sub-Dittert function.
- **Earlier complete square proof:** Pedro Paulo Marques do Nascimento's
  [public Dittert project](https://github.com/pedromnasc/dittert-conjecture-proof/tree/894066bbaa715138c98bf3cb7c6fdb4f39a37701),
  including Hongyuan Lu's attributed small-order contribution. Its July 26
  unified argument covers n>=11 without Pang's endpoint theorem. A complete
  assembled route passed our separate local audit of analytic reductions and
  independently reconstructed exact certificate checks. No substantive gap
  was found; journal acceptance and formal verification were not established.
  Our square result must be described as an alternative proof, not a first
  resolution. The audit is not imported as a proof or formal dependency.
- **Minimum dilation and domination:** Gi-Sang Cheon and Ian M. Wanless,
  [Some results towards the Dittert conjecture on permanents](https://users.monash.edu.au/~iwanless/papers/DittertIndecompLAA.pdf),
  Linear Algebra and its Applications 436 (2012), 791–801. Lemma 2.3 supplies
  the minimum-dilation antecedent; Lemma 2.2 credits the domination criterion
  to C.-K. Li. This is a different paper from the 2007 interpretation.
  The rectangular transport, minimum and active cuts are proved internally.
- **Boundary scaling and ratio method:** Zhekai Pang,
  [arXiv:2606.01531v1](https://arxiv.org/abs/2606.01531v1), supplies the method
  adapted in the endpoint boundary arguments. His theorem is for square
  dimensions n>=17, not arbitrary rectangles. The
  [boundary source note](BOUNDARY_PERMANENT.md) retains the Knopp–Sinkhorn
  attribution through Pang and distinguishes the internally proved floor
  from the original paper, which was not independently used here.
- **Other square literature:**
  [Kafidov, arXiv:2607.19439v1](https://arxiv.org/abs/2607.19439v1), and
  [Li–Xiong–Yang, arXiv:2607.29191v2](https://arxiv.org/abs/2607.29191v2).
  Their square endpoint scope is not widened to rectangles or intermediate orders.
- **Conditional local lemma:** Bernhard Haeupler, Barna Saha and Aravind
  Srinivasan, [New Constructive Aspects of the Lovasz Local Lemma](https://arxiv.org/abs/1001.1231v5).
  Its conditioning framework is adapted in the collision strips. The finite
  weighted-sum argument and actual independence are proved internally;
  no resampling algorithm or external probability axiom is claimed.
- **Van der Waerden prerequisite:** Leonid Gurvits,
  [stable homogeneous polynomial capacity proof](https://arxiv.org/abs/0711.3496v2),
  Electronic Journal of Combinatorics 15 (2008), R66; and Monique Laurent
  and Alexander Schrijver,
  [On Leonid Gurvits' proof for permanents](https://ir.cwi.nl/pub/16667),
  American Mathematical Monthly 117 (2010), 903–911. The latter supplies
  the selected matrix-specific equality route. [CAPACITY-ROUTE](CAPACITY-ROUTE.md)
  identifies the completed formal capacity and stability prerequisites
  and the zero-capacity boundary correction when reading the univariate
  equality statement.

- **Two-zero permanent face:** Kyle Pula, Seok-Zun Song and Ian M. Wanless,
  [Minimum permanents on two faces of the polytope of doubly stochastic matrices](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-1022.pdf)
  (2011), supplies the repeated-support face and reduced scalar model context.
  The [actual matrix reduction](TWO_ZERO_REDUCTION.md), Alexandrov inequality,
  feasible averaging and [quantitative floors](TWO_ZERO_PERMANENT.md) are
  proved internally, allowing arbitrary additional zeros.

The informal source of this development is Analytic-Lab P0174, audited at
`bdce7f70f49d8b79ee756df6724ed3822e0c7f20` and integrated on main at
`1be1af0f8e9346bdd32a80745537bde916f004f7`. The private Lab retains the
complete proof notes, sources and independent replay archive (108 executions,
69 source fingerprints). Those are informal and computer-assisted evidence,
not substitutes for the proofs required in this repository.

Our square argument uses supported-cell stationarity, an explicit singular
pair and balanced spectral cuts, with separate small-order arguments. Our
all-order rectangle argument uses collision concentration and strict matrix
averaging. Shared established permanent and transport theory keeps its
attribution and must be proved or found in trusted Lean dependencies.
Novelty beyond the bounded source comparison has not been established.

The linked proof accounts accompany the actual formalized proofs. Readers
need no private Lab access to inspect theorem hypotheses or replay the
complete proof repository.
