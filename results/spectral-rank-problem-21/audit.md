# Ordered spectral proximity forces adjacency rank at most five

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## What Lean proves

Let \(n\ge3\) and let \(H\) be a finite simple graph on \(3n\) vertices. List its real adjacency eigenvalues in nonincreasing order with multiplicities. If the sum of squared differences from the ordered sequence \((2n,0,\ldots,0,-n,-n)\) is strictly less than \(2/3\), then the real adjacency matrix of \(H\) has rank at most five.

This answers Problem 21 of Jovanović, Sedlar and Škrekovski, and does not require \(H\) to be connected. The strict threshold applies to the **sum of squares**, not its square root and not the Manhattan distance. The separate cospectrality minimizer and uniqueness Conjecture 20 is not addressed.

- [Exact Lean statement](../../SpectralRank/SpectralTop.lean): SpectralRank.problem_21.
- [Mathematical proof and finite certificates](proof.md).
- The default build checks `SpectralRank.problem_21` and the publication gate audits its axioms. Palomar separately compared the Challenge and Solution at commit `7846ef8`. [Local verification](../../docs/verification.md) · [Registered comparison](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000004&version=1).

The Lean theorem represents the graph by a symmetric zero-diagonal Boolean adjacency function on \(\mathrm{Fin}(3n)\), casts it to a real adjacency matrix, and derives the Hermitian condition from symmetry. Mathlib's ordered eigenvalue sequence supplies the order and multiplicities. Lean checks all finite cases with exact integers, using the ordinary kernel rather than floating point, native certificates, or an assumed graph catalogue.

## Sources and overlap audit (2026-11-26)

- [Irena M. Jovanović, Jelena Sedlar and Riste Škrekovski, arXiv:2610.18636v2, §5](https://arxiv.org/html/2610.18636v2#S5): the displayed squared distance immediately before Problem 21 is the definition used here. The problem is in v2, revised 2 November 2026; the original v1 does not contain it.
- [Jovanović, Sedlar and Škrekovski, arXiv:2611.26650v1](https://arxiv.org/abs/2611.26650v1): this follow-up concerns Manhattan cospectrality of cocktail party graphs, not Problem 21.
- [Richard Brualdi, Louis Deaett, Dale Olesky and Pauline van den Driessche, *The principal rank characteristic sequence of a real symmetric matrix*](https://www.sciencedirect.com/science/article/pii/S0024379511007567): prior principal-minor theory gives the structural reduction to order six or seven. The Lean development proves the needed reduction directly. The prior result does not give the spectral threshold. The rank-four and rank-five graph classifications cited in the source problem are downstream tools, not a proof of the rank bound.

A bounded search by exact problem, article, author names and related terminology, including arXiv and public mathematics and formalization indexes, found no explicit prior resolution. This is not a priority claim. A separate AI review compared the exact statement and checked the citation boundaries; no external author endorsement or human refereeing is claimed.
