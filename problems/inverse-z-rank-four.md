# Inverse Z-polynomials are log-concave in ranks at most four

**Status:** Written partial proof, separately AI-reviewed. The general conjecture and priority are not settled here. No Lean formalization is provided. The proof does not assume representability or the sparse paving property.

[Gao–Ruan–Xie, arXiv:2507.01332v1, Conjecture 1.5](https://arxiv.org/html/2507.01332v1) conjecture that every matroid's inverse $Z$-polynomial has log-concave coefficients and no internal zeros. Their Theorem 1.6 proves the sparse paving case (see also the [journal article](https://www.sciencedirect.com/science/article/pii/S0097316526000634)). We prove the conjecture for all matroids of rank at most four.

## Coefficient identities

Write $\mu(F,G)$ for the Möbius function of the lattice of flats and put $m(F,G)=(-1)^{\operatorname{rk}(G)-\operatorname{rk}(F)}\mu(F,G)$. The alternating-sign theorem for geometric lattices gives $m(F,G)>0$ (see the characteristic-polynomial discussion in Gao–Ruan–Xie, Proposition 2.1). Write $0,1$ for the bottom and top flats. From Gao–Ruan–Xie equations (2)–(3) and Lemma 2.2, or [Braden–Ferroni–Matherne–Nepal, Theorem 2.2](https://arxiv.org/html/2510.01086v2#S2.SS2), the palindromic polynomial $Y_M$ of rank $r$ satisfies
$$
Y_M(t)=\sum_{F\in\mathcal{L}(M)}m(F,1)t^{r-\operatorname{rk} F}Q_{M|F}(t),
\qquad \deg Q_N<\tfrac12\operatorname{rk}(N)\quad(\operatorname{rk}(N)>0),
$$
where the rank-zero $Q$ is 1. The top coefficient is $m(0,1)$ by the degree bound, hence so is the constant coefficient of $Y_M$. Only the top flat can contribute to that constant term, so $Q_M(0)=m(0,1)$.

By definition $Y_M$ is unchanged by deleting loops. A loopless matroid and its simplification have isomorphic ranked flat lattices, so the polynomial is also unchanged by simplification; see Gao–Ruan–Xie, proof of Proposition 5.3, or Theorem 2.2 and its incidence-algebra interpretation in the second reference. Thus suppose $M$ simple.

Rank zero gives $Y=1$ and rank one gives $Y=1+t$. In rank two with $n$ points, the coefficient sequence is $(n-1,n,n-1)$, using $m(0,1)=n-1$ and the $n$ rank-one summands. Here $n\ge2$.

In rank three let $n$ be the number of points, $L$ the number of lines, and $d=\sum_\ell |\ell|$ the point-line incidence count. The Möbius recurrence at the top gives $[t^3]Y=m(0,1)=d-L-n+1$. Only point summands contribute to $[t^2]Y$: $M/p$ has rank two and has one point for each line through $p$, so the coefficient is $d-n$. Thus the sequence is $(a,b,b,a)$ with $b-a=L-1>0$. Also
$$
[t]Q_M=b-\sum_{\ell}m(0,\ell)
=(d-n)-(d-L)=L-n.
$$
This identity applies to each rank-three restriction. In ranks zero and one, log-concavity is vacuous; in ranks two and three, positivity and the displayed ordering give every log-concavity inequality directly.

For rank four use $W_i$ for the number of rank-$i$ flats, $I_{ij}$ for the number of incidences between a rank-$i$ and a rank-$j$ flat, and $T$ for the number of point–line–plane flags. Let $Y$ have coefficient sequence $(A,B,C,B,A)$. Then
$$
\begin{aligned}
 A&=T-I_{23}-I_{13}+W_3-I_{12}+W_2+W_1-1,\\
 B&=T-I_{13}-I_{12}+W_1,\\
 C&=T-I_{12}+W_2-I_{13}.
\end{aligned}
$$
Indeed, for $A=m(0,1)$ apply the Möbius recurrence, expanding the contribution of each plane $H$ by the rank-three formula. For $B=[t^3]Y$, only points contribute, and $m(p,1)$ is the number of line–plane flags through $p$ minus the numbers of planes and lines through $p$, plus 1, again by the rank-three formula applied to $M/p$. For $C=[t^2]Y$, each line $\ell$ contributes $(|\ell|-1)(h_\ell-1)$ where $h_\ell$ is the number of planes through it. Each plane $H$ contributes $[t]Q_{M|H}$, its number of lines minus its number of points. Summing gives $C=(T-I_{12}-I_{23}+W_2)+(I_{23}-I_{13})$.

## Rank-four deletion inequality

Set
$$
 D=(B-A)-(C-B)=I_{23}-2W_2-W_3+W_1+1.
$$
We prove the stronger bound $D\ge W_1-3$. Choose a basis of the simple rank-four matroid and delete each nonbasis point in turn, preserving rank four. For one such deletion write $e$ for the removed point, and use $\Delta$ for a count in $M$ minus the corresponding count in $M\setminus e$.

Call a flat old if it comes from the following closure embedding; otherwise call it new. Flats of the deletion are in rank- and inclusion-preserving bijection, via $F'\mapsto\operatorname{cl}_M(F')$, with flats $F$ of $M$ such that $\operatorname{rk}_M(F\setminus e)=\operatorname{rk}_M(F)$. The inverse is $F\mapsto F\setminus e$. Indeed, closure in a restriction is the intersection with its ground set of the original closure. Conversely when $F\setminus e$ has full rank in $F$ it spans $F$. Thus any incidences between two such old flats are preserved in both directions, and any new flat contains $e$ as a coloop of its restriction.

Let $\mathcal N_2$ be the new lines and $\mathcal N_3$ the new planes. Each new line is a two-point line through $e$, by simplicity and the rank-drop characterization. A new plane $H$ has exactly one old line: $H\setminus e$ is a rank-two flat of $M$ since $e$ is outside its closure and $H$ is a flat. Every old line in $H$ has a rank-two trace in $H\setminus e$, hence its closure is this same line. It follows that all new line–plane incidences are disjointly counted by the $h_\ell$ incidences for each new line and by one old-line incidence for each new plane. In particular,
$$
\Delta I_{23}=\sum_{\ell\in\mathcal N_2}h_\ell+|\mathcal N_3|.
$$
Because the matroid is simple, the deleted point lowers $W_1$ by one. Therefore
$$
\Delta D=1+\sum_{\ell\in\mathcal N_2}(h_\ell-2)\ge1;
$$
a rank-two contraction $M/\ell$ has at least two rank-one flats, so $h_\ell\ge2$. The Boolean rank-four lattice has $W_1=4$, $W_2=6$, $W_3=4$, $I_{23}=12$, so $D=1$. Reverse the deletions to obtain $D\ge W_1-3$.

Finally $C-B=W_2-W_1\ge0$ by the point–line inequality, which here has a short direct proof. If $N$ is the point-by-line incidence matrix, distinct points lie on exactly one common line and each point belongs to at least two lines (otherwise the entire matroid has rank at most two). Thus $NN^\mathsf{T}=J+\operatorname{diag}(d_p-1)$, where $J$ is all ones and $d_p$ counts the lines through $p$. This is positive definite, so columns number at least rows.

Now $x=B-A\ge y=C-B\ge0$. Since $A>0$ and $x-y\ge W_1-3\ge1$, we have
$$
 B^2-AC=A(x-y)+x^2>0,
 \qquad C^2-B^2\ge0.
$$
The coefficients are positive and palindromic. This proves the rank-four case of the conjecture and completes the proof for ranks at most four.

## Exact computational checks

The accompanying standard-library program is a check on the formulas, not a premise of the proof.

```sh
python inv_z.py --rank4-all
python inv_z.py --seed 117 --trials 150
```

The first run enumerates each of the 32,767 nonempty subsets of the 15 points of $\mathrm{PG}(3,2)$. Every simple binary matroid of rank at most four occurs up to isomorphism among these subsets, but the counts below are labelled subsets, not isomorphism counts. The number at ranks one through four was 15, 140, 1,380, and 31,232. All checks passed. The smallest adjacent coefficient ratio $a_i^2/(a_{i-1}a_{i+1})$ over the rank-four samples was $49/36$, attained by $\mathrm{PG}(3,2)$ with coefficients $(64,120,140,120,64)$. For every rank-four input, the program compares the inverse-KL lattice recurrence with the flag formulas above and checks $D\ge W_1-3$ exactly.

The second run checked 450 seeded draws, 150 in each ambient dimension 4, 5, and 6. All checks passed, but the higher-rank search is only a sample. For the first ten cases of each run and for the basis, triangle, and projective-geometry baselines, we also compute the ordinary $Z$-polynomials independently and invert them in the incidence algebra, checking the sign-normalized result against the primary computation.

## Computational checks

The proof applies to arbitrary matroids, not only representable ones. As a
separate implementation check, the dependency-free Python script computes
inverse polynomials from the flat lattice and checks the rank-four formula.
It also uses an incidence-algebra inversion of the ordinary Z-polynomial
as an independent spot check.

```sh
python experiments/inverse_z_binary.py --rank4-all
python experiments/inverse_z_binary.py --seed 117 --trials 150
```

The first command checks all 32,767 nonempty point subsets of the
15-point binary projective space, retaining labeled duplicates. The
counts in ranks 1–4 are 15, 140, 1,380, and 31,232. The seed-117 run checks
450 random binary instances drawn in ambient dimensions 4, 5, and 6.
These are sanity checks, not the proof, and they do not prove any general
rank-five or rank-six statement.
