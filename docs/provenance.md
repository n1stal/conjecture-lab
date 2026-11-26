# Provenance and citation

Jaime Nistal leads Conjecture Lab and is listed as the author. Codex (OpenAI) is credited as an AI co-author for assistance with exploration, proofs, code, documentation, and verification. AI-assisted review is not independent human peer review. Its experiments were inspired by the [Cinna Davis and GPT-6.2 Astra conjecture catalogue](https://github.com/1337isnot1337/solved-conjectures). This repository is a separate project, not a fork or an extension of that catalogue's mathematical results. It has not been peer reviewed.

## Problem sources

- Pavel Chebotarev, [arXiv:2610.14100v4, §7.3, Question 2](https://arxiv.org/html/2610.14100v4#S7.SS3), and the [companion study](https://arxiv.org/html/2611.02249#S7). Version v4 matters: it settles order four and records a limited order-six unweighted sample and fractional-weight examples. See the [result note](../problems/chebotarev-q2.md) for exact distinctions.
- [Erdős Problems, #982](https://www.erdosproblems.com/982); [literature summary](https://erdosproblems.ai/wiki/problems/distance_problems/E0982); and [prior search notes](https://lemmapark.com/programs/erdos-open/challenges/Lemma.erdos_982). The result here is only for a symmetric subclass.
- [Erdős Problems, #12](https://www.erdosproblems.com/12); Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer, [The three parts of Erdős Problem 12: counting functions and reciprocal sums](https://hexagonmath.org/2611.00765v1), Theorem 1.3. A uniform bound and its optimal value are different questions.

## How to cite an entry

Cite the *specific result note*, the repository commit, and the scope, not just the parent conjecture. For example: *Jaime Nistal and Codex (OpenAI), “Exact containment in the entire order-six polygon” (unweighted six-vertex case), Conjecture Lab, commit `<SHA>`.* The [citation file](../CITATION.cff) provides repository-level metadata. If citing the original question or another author's theorem, cite that source directly.

## Commit attribution

For future contributions by Codex under Jaime’s direction, use Jaime Nistal as the Git author and include `Co-authored-by: Codex <codex@openai.com>` in the commit message. Do not rewrite existing history.
