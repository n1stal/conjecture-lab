# The exact companion quartic for three nondeterministic steps

Jaime Nistal. Proof development and Lean formalization with Codex (OpenAI).

Let E(t) count words over A={−1}, B={−1,+1}, C={−2,+1} for which there is
a selection of signed steps that keeps every partial sum nonnegative and
ends at zero. A word is counted once, regardless of its number of
realizations. We prove P(t,E(t))=0, where P is exactly the polynomial
assigned to algEE in the [authors' Maple companion](https://gitlab.com/api/v4/projects/53488626/repository/blobs/62f9f05364094361e768ace519a10aec3772d345/raw).
[Section 6.2](https://arxiv.org/html/2311.03234v2#S6.SS2) leaves its
correctness open after checking finitely many coefficients. The Challenge
contains the full integer coefficient lists, not an approximation to P.

## 1. Recognize the source words exactly

For a feasible prefix, let h be the highest reachable height. Choosing
the greatest element of each letter achieves that height. Record the
deficits of attainable heights from h in a set S. Initially h=0 and
S={0}. An A decreases h by one and discards deficits above the new h;
it fails at h=0. A B or C raises h by one and takes the union of S and a
shift of S by 2 or 3, respectively, retaining only elements at most the
new h. The prefix is accepted exactly when h belongs to S.

Below height 5, eleven literal finite sets suffice. At higher heights
there are seven phases, determined by congruence modulo 2 or 3 and a
small number of endpoint holes. The proof checks their transition
formulas for every possible high height, the finite boundary transitions,
and the exact acceptance condition. The phase machine is deterministic,
so it counts words rather than witnesses.

## 2. Decompose paths without overcounting

Write R_b for the matrix of phase-tagged returns to a high base b that
never go below b, and M_b for the column of all high-band paths that end
accepted. Let U_b and D_b denote the up and down one-step operators,
including the factor t, and let F_b be the high acceptance vector.

A nonempty return factors uniquely into an up letter, an inner return
at the next base, the matching down letter, and a remaining return.
An accepted high-band path either has no return after its first up step
or has the same first-return factor followed by a terminal path.
Therefore, with products interpreted as Cauchy series products,

    R_b = I + U_b R_(b+1) D_(b+1) R_b
    M_b = F_b + U_b M_(b+1) + U_b R_(b+1) D_(b+1) M_b.

The high system has period six in its base. A high entry at height 5
either never exits the band or returns to its base, takes its first
exit, and follows a low continuation. With high entry vector E_high,
low continuation vector X, low flags f, low-transition matrix L,
and entry and exit matrices G and D_exit, this gives

    E_high = M_5 + R_5 D_exit X
    X = f + L X + G E_high.

Each factorization is unique. The proof checks the resulting recurrence
for every coefficient and proves uniqueness coefficient by coefficient.
The source series is the coordinate of X for the empty prefix.

## 3. Evaluate the exact system

The phase order makes the return matrices upper triangular. Their
diagonals are ordinary Catalan series of up multiplicity 1 or 2, or 1
for transient states. For each upper-triangular gap, the six residue
equations are linear in entries of that gap, with the smaller gaps
already fixed. This yields explicit entries in the field generated
by the regular branches of sqrt(1−4t²) and sqrt(1−8t²).

The formal proof works in the ring of rational sequences with Cauchy
multiplication. It constructs both constant-one square roots and
cancellation and quotient operations on coefficients. Exact normalized
polynomials certify the displayed matrix equations. The initial
coefficients checked in this step establish divisibility of the
numerators by the known monomial factor of their common denominator;
they are not a finite scan of the claimed sequence identity. All
matrix equations, their formal solution, and the final substitution of
the entire word-count series into P are checked in Lean.

The compared declaration is PalomarWalkQuartic.exact_quartic. The
claim is the exact unweighted equation. It does not assert a minimal
algebraic degree, any weighted extension, or the paper's separate
general Conjecture 6.7.
