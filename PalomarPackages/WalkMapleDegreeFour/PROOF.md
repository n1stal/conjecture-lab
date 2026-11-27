# Minimum algebraic degree of the Section 6.2 excursion series

Jaime Nistal. Proof development and Lean formalization with Codex (OpenAI).

Let $E(t)$ count distinct words over $A=\{-1\}$, $B=\{-1,+1\}$,
$C=\{-2,+1\}$ with at least one signed realization whose partial sums
remain nonnegative and whose final sum is zero. A word is counted once,
not once per realizing walk. This is the unweighted three-letter model
in [de Panafieu–Wallner, §6.2](https://arxiv.org/html/2311.03234v2#S6.SS2).
The exact polynomial $P(t,Y)$ is the assignment algEE in the
[authors' Maple companion](https://gitlab.com/api/v4/projects/53488626/repository/blobs/62f9f05364094361e768ace519a10aec3772d345/raw).
**The minimum degree of an annihilating polynomial in $\mathbb Q(t)[Y]$ is four.**
The result goes beyond proving that the indicated quartic vanishes. It
does not claim a weighted generalization or settle Conjecture 6.7.

## The upper bound and exact numerator

For each prefix, track the maximum reachable height and the set of deficits
of other reachable heights from that maximum. The controller handles all
heights below 5 explicitly and handles the remaining heights with seven
phases. It checks the original word membership, all transition rules,
and exact acceptance. A first-return/first-exit decomposition gives the
complete coefficient recurrences. A six-period high-state solution
evaluates those recurrences and is proved unique coefficient by coefficient.

The constructive solution produces $dE=N$, where $d\in\mathbb Z[t]$ is
nonzero and $N$ is a polynomial in $t,R,S$ with $\mathbb Z[t]$ coefficients,
$R^2=1-4t^2=F$, and $S^2=1-8t^2=G$, using the branches with constant term
one. The checks give $P(t,E(t))=0$ and separately show that its leading
coefficient is nonzero (its degree-8 coefficient in $t$ is 4). This is
identical to the source companion's quartic, not a polynomial substituted
for convenience.

## The lower bound via four conjugates

Work in rational formal series with Cauchy multiplication, an integral
domain by the leading coefficient of any nonzero series. The three
polynomials $F,G,FG$ are not squares in $\mathbb Q(t)$. For a putative
fraction-free identity $A(t)^2=H(t)B(t)^2$ with $B\ne0$, translate by 1
for $H=F,G$ and by $2/5$ for $H=FG$. Translation preserves the highest
nonzero polynomial coefficient. The first nonzero coefficients on the
two sides must then have opposite signs: the translated constant terms
of $F,G,FG$ are respectively $-3,-7,-63/625$. Consequently $1,R,S,RS$
are independent over $\mathbb Q(t)$. To see this directly, multiply
$A+BR+CS+DRS=0$ by $C-DR$ and write the result as $X+YR+ZS=0$. If $Z\ne0$,
squaring gives $XY=0$ by independence of $1,R$, and the remaining
equation makes either $G$ or $FG$ a square. If $Z=0$, nonsquareness of
$F$ first shows $C=D=0$, then $A=B=0$. All arguments are implemented
without dividing by a series with zero constant term.

The independent coordinates of $N$ along both $R$ and $S$ are nonzero,
so the four sign substitutions $R\mapsto\pm R,\ S\mapsto\pm S$ produce
distinct values of $N$. If a cubic over $\mathbb Q(t)$ annihilates $E$,
first clear the product of all four coefficient denominators, then use
$dE=N$ to turn the relation into a cubic on $N$. Independence of the four
basis elements implies the same cubic annihilates all four sign values.
A cubic over an integral domain cannot have four distinct roots; the
formal proof implements this by factor deflation and cancellation. It
follows that all four original polynomial numerators are zero, even
if one or more rational-function coefficients initially has a pole
at $t=0$.

## Compared declaration

The compared theorem is PalomarWalkQuarticDegree.minimum_degree_four.
The Challenge stores the complete low-degree-first integer coefficient lists
of the author polynomial and applies the cleared cubic relation to the
same literal full source word-count series. Integer-polynomial numerators
and denominators represent all of $\mathbb Q(t)$, since rational constants
may be cleared in each pair, and denominators are required nonzero. The
upper and lower bounds are simultaneous conclusions of this theorem.
