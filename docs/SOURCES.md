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
- **Related square literature:**
  [Pang, arXiv:2606.01531v1](https://arxiv.org/abs/2606.01531v1),
  [Kafidov, arXiv:2607.19439v1](https://arxiv.org/abs/2607.19439v1), and
  [Li–Xiong–Yang, arXiv:2607.29191v2](https://arxiv.org/abs/2607.29191v2).
  These concern square endpoint cases. Their scope is not silently widened
  to arbitrary rectangles or intermediate orders.
- **Van der Waerden prerequisite:** Leonid Gurvits,
  [stable homogeneous polynomial capacity proof](https://arxiv.org/abs/0711.3496v2),
  Electronic Journal of Combinatorics 15 (2008), R66; and Monique Laurent
  and Alexander Schrijver,
  [On Leonid Gurvits' proof for permanents](https://ir.cwi.nl/pub/16667),
  American Mathematical Monthly 117 (2010), 903–911. The latter supplies
  the selected matrix-specific equality route. [CAPACITY-ROUTE](CAPACITY-ROUTE.md)
  identifies completed formal prerequisites, remaining stability obligations
  and the zero-capacity boundary correction when reading the univariate
  equality statement.

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

The release will include a self-contained informal account of the actual
formalized proofs. Public readers must not need access to a private Lab
repository to understand a theorem, inspect its assumptions, or replay it.
