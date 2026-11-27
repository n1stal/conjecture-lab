# Parallel-pair, support-star, and double-star obstructions in Erdős Problem 617

**Jaime Nistal**, responsible author. **Codex (OpenAI)**, AI co-author for proof development and Lean formalization.

This enhanced package retains the earlier pair and star results and adds a palette-counting exclusion for a class of normalized double stars. A balanced r-coloring is an edge coloring in which every set of r+1 distinct vertices sees all r colors. The formal results are conditional on the precise two-anchor support geometry and scoped core independence and clique bounds stated in the Challenge. They do not prove the unrestricted [Erdős Problem 617](https://www.erdosproblems.com/617).

- **Pair bound:** for r≥12 and row deficits d,e≥3, if d+e≤r−3 then at most d+e−2 exceptions have the two anchors as their exact support. This is the earlier formalized result, included unchanged as the local ingredient.
- **Refined star:** if each spoke meets the explicit pentagon-split conditions and every row's strict palette budget holds, an actual normalized star with one excess exception cannot exist.
- **Uniform star family:** if the hub deficit is D≥3, every leaf has deficit 3≤e≤D and e+1 incident exceptions on its spoke, and r≥(D+1)², such a normalized star is impossible. Leaf deficits may differ.
- **Uniform double-star family:** if all row deficits lie between 3 and D and r≥ceil(49D²/64)+6D+10, a normalized two-hub support cannot exist. Each leaf is incident with a genuine spoke of positive surplus; the two hubs share the central exception bundle.

[PROOF.md](PROOF.md) proves the new results and [PAIR-PROOF.md](PAIR-PROOF.md) gives the retained pair proof. The pair and two star theorem statements are unchanged; the uniform double-star theorem is the added compared endpoint. [Challenge.lean](Palomar/Erdos617PairStarDouble/Challenge.lean) imports only Std and has one placeholder for each compared theorem. The independent Solution and its support do not import Challenge. The four arithmetic helper definitions used in the public statements are included in comparator.json.

The pinned compiler is Lean 4.35.0-rc2. Run `lake build` and `./replay.sh`. For the supported further comparison, run `lake comparator --config comparator.json` in an environment that supports its sandbox. No hosted check, registration, publication, or human peer review for this enhanced package is claimed.
