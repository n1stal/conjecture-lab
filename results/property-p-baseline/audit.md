# Property P finite-witness audit

Checked 2026-11-26. Scope: admissibility of the set {1, 2} and its reciprocal sum, not optimality at any cutoff or a general upper bound.

## Source and priority

- [Erdős Problem 12](https://www.erdosproblems.com/12): formulation and attribution.
- [Howe, Huffman, Kohlmeyer and Kruer](https://hexagonmath.org/2611.00765v1), §1: Property P and the distinct question of a uniform reciprocal bound.

Checked the primary formulation and related results using “Erdős Problem 12,” “Property P,” and “reciprocal sum.” This is an elementary baseline, not a discovery or a priority claim. With two elements there is no triple to check. The arithmetic uses the common denominator two.

## Exact Lean scope

`ConjectureLab.baseline_valid` checks the Boolean predicate on the finite list `[1, 2]`. The ordered triple condition in the predicate is equivalent to either order of the larger two distinct members. `ConjectureLab.baseline_weight` checks the exact integer-scaled sum for that pair. Neither declaration is a finite optimum, a global bound, or a resolution of Erdős Problem 12.
