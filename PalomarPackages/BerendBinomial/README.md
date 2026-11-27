# Reflection of exceptional breakpoints for k-wise independent bits

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

This proves [Berend–Ernst–Kontorovich–Kumar, Conjecture 5.11](https://doi.org/10.1007/s10959-026-01487-4): for even \(k\) with \(2\le k\le n-1\), every exceptional interior breakpoint \(p\) of the binomial-moment optimization has a reflected exceptional breakpoint at \(1-p\). Exceptional means that the realizable basis loses at least two indices at the transition. It does not claim rationality of these points or any theorem about the lexicographic indexing of bases.

## Correspondence to the source

The source LP (29)–(31) uses a nonnegative law \(w\) on the integer grid \(0,\dots,n\) and matches the binomial moments of \(\operatorname{Bin}(n,p)\) through order \(k\). Its \(j\)-th test is the evaluation of a polynomial:
\[
\binom{x}{j}=\frac{x(x-1)\cdots(x-j+1)}{j!}.
\]
For \(j=0,\dots,k\) these polynomials have distinct degrees \(j\) and nonzero leading coefficients \(1/j!\). The triangular change of basis from monomials makes them a basis of the polynomials through degree \(k\). Thus matching these tests is equivalent to the formal definition of **Quadrature**, which matches all polynomial tests through degree \(k\). Its binomial law is the literal probability \(\binom{n}{x}p^x(1-p)^{n-x}\) on this grid. In particular the constant test normalizes the law.

By the source's Theorem 3.3, for even \(k\) a dual-feasible basis consists of the fixed endpoint \(n\) and \(k/2\) disjoint consecutive pairs of lower nodes. The formal predicate **Paired** spells out that form; **Feasible** requires a nonnegative quadrature supported on the permitted basis positions (some basis weights may be zero). **Exceptional** requires shared feasibility at the internal breakpoint and feasibility of the old and new bases throughout one-sided neighborhoods, together with at least two departing lower nodes. The fixed node \(n\) cancels in the difference. Reflection interchanges old and new, and their equal sizes make the departing and arriving counts equal.

There is an endpoint distinction in the paper's notation \(L(I)\): at \(p=1\) every basis containing \(n\) is feasible because all mass lies at \(n\), even if its positive-length feasible interval ended earlier. The formal endpoint explicitly concerns \(0<p<1\) and actual one-sided activity, so that isolated endpoint does not create a transition.

## Proof idea

Multiply each test polynomial \(f(x)\) of degree at most \(k-1\) by \(n-x\). This kills the mass at \(n\), and the identity
\[
(n-x)\binom n x=n\binom{n-1}{x}
\]
reduces the lower-node weights to quadrature for \(\operatorname{Bin}(n-1,p)\), after dividing by \(n(1-p)\). This gives an equivalence of feasibility: in the reverse direction the lower weights determine the mass at \(n\) from the constant test, and that mass is nonnegative because it is proportional to the binomial expectation of \(\prod_a (x-a)(x-a-1)\), over the paired starts \(a\). This polynomial vanishes on the lower basis nodes and is nonnegative on the integer grid.

Reflecting the reduced grid by \(x\mapsto n-1-x\) sends its binomial law at \(p\) to its binomial law at \(1-p\), preserves the polynomial degree bound, and takes adjacent pairs to adjacent pairs. It therefore transports feasibility. Applying this on each side of an exceptional breakpoint reverses the time order of the two bases and preserves the number of changing indices.

## Formal statement and verification

- `Palomar/BerendBinomial/Challenge.lean`: isolated statement importing only Mathlib. The intentional admission is in this statement-only file.
- `Palomar/BerendBinomial/Solution.lean`: standalone proof importing only Mathlib.
- Comparator endpoint: `BerendBinomial.source_exceptional_reflect`.
- Lean 4.35.0-rc2; Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The standalone Solution passed Lean at this pin with warnings as errors. The endpoint depends only on `propext`, `Classical.choice`, and `Quot.sound`. The Challenge elaborated separately, with only its intentional statement-admission warning. This package is not yet registered or human-reviewed. The paper's basis characterization is credited to its cited Boros–Prékopa work.
