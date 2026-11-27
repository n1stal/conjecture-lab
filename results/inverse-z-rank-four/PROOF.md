# Inverse Z-polynomial log-concavity through rank four

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## Statement

Let $M$ be a finite matroid of rank $r\le 4$, and write $Y_M(t)=\sum_i a_i t^i$ for its inverse $Z$-polynomial, in the normalization of Gao, Ruan, and Xie. Then $a_i>0$ for $0\le i\le r$, $a_i=0$ for $i>r$, and
$
a_i a_{i+2}\le a_{i+1}^{\,2}\qquad(i\ge 0).
$
There is no assumption of representability or simplicity. This is the rank-at-most-four case of [Gao–Ruan–Xie, Conjecture 1.5](https://arxiv.org/html/2507.01332v1); this proof does not settle log-concavity in higher rank.

The exact Lean statement is [ConjectureLab.Submission.inverse_z_rank_at_most_four](https://github.com/RokaSwK/conjecture-lab/blob/fba1c28396deea5482f5f38f077c6117c49dbf8e/Solution.lean). The [Palomar record](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000061&version=1) identifies the checked commit, and the [verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45876926926) records the mechanical check. Below is a written proof, including the rank-four incidence and deletion arguments.

## 1. The flat-lattice description

Let $0$ and $1$ denote the bottom and top flats, and put
$
u(F,G)=(-1)^{\operatorname{rk}G-\operatorname{rk}F}\mu(F,G)
$
for the sign-adjusted Möbius function of the flat lattice. Write $Q_{F,G}(t)$ for the inverse Kazhdan–Lusztig polynomial of the interval $[F,G]$. The [characterization of Braden–Ferroni–Matherne–Nepal, Theorem 2.2](https://arxiv.org/html/2510.01086v2) gives
$
Y_{F,G}(t)=\sum_{F\le X\le G}
  u(X,G)t^{\operatorname{rk}G-\operatorname{rk}X}Q_{F,X}(t).
$
Here $Q_{F,F}=1$; on an interval of positive rank $d$ the degree of $Q$ is less than $d/2$; and $Y_{F,G}$ is palindromic about degree $d/2$. These rules determine the polynomials by induction: after summing over $X<G$, the low coefficients of the missing $Q_{F,G}$ are precisely the differences needed to match the corresponding high coefficients of that sum, and all its remaining coefficients vanish. The degree bound in the sum gives $\deg Y_{F,G}\le d$. For $d>0$, only $X=F$ can contribute at degree $d$, so
$
[t^d]Y_{F,G}=[t^0]Y_{F,G}=Q_{F,G}(0)=u(F,G).
$
Also, only the relative rank-one flats $X$ contribute at degree $d-1$: the rank-zero term is a pure $t^d$ term; for relative rank $j\ge2$ the shift leaves degree $j-1$ to $Q_{F,X}$, which is forbidden by its degree bound. We use both observations below.

Removing loops and then choosing one representative of each parallel class preserves the ranked lattice of flats. Indeed, every flat contains all loops and is a union of parallel classes, and its trace on the chosen representatives spans it. The trace and closure maps are inverse rank-preserving order isomorphisms. We may therefore work with the simplification, and its rank-one flats are its individual points.

We will use $u(0,G)>0$. Here is a short argument. For a positive-rank flat $G$, choose a point $e\le G$. For each flat $H\le G$ containing $e$, let $S_H=\sum_{F\vee e=H}\mu(0,F)$, where $F$ ranges over flats under $G$. Then
$
\sum_{e\le H\le K}S_H=\sum_{F\le K}\mu(0,F)=0
\qquad(e\le K\le G).
$
Induction on that interval gives $S_G=0$. Every proper $F$ in the fiber $F\vee e=G$ has rank $\operatorname{rk}G-1$: $e\notin F$, and adding one point raises the rank by one. There is at least one such $F$, obtained by extending $e$ to a basis of $G$ and closing the basis with $e$ removed. Rearranging $S_G=0$ and adjusting signs therefore expresses $u(0,G)$ as a nonempty sum of positive $u(0,F)$, by induction from $u(0,0)=1$.

## 2. Coefficients through rank four

Write $W_i$ for the number of rank-$i$ flats, $I_{ij}$ for the number of incidences $F_i<F_j$ between flats of ranks $i,j$, and $T$ for the number of flags $F_1<F_2<F_3$. Points, lines, and planes have ranks $1,2,3$ respectively. When these symbols are used for a proper interval, ranks are measured from its bottom.

The Möbius recurrence gives $u=1$ in rank one and $u=W_1-1$ in rank two. In rank three it gives
$
u=I_{12}-W_2-W_1+1,
$
because summing $u(0,L)$ over lines gives $I_{12}-W_2$, and each point has $u=1$. The penultimate coefficient in rank three is $\sum_{p}u(p,1)=I_{12}-W_1$, by the rank-two formula in each interval $[p,1]$. Consequently, for a rank-three interval, its inverse Kazhdan–Lusztig coefficient is
$
[t]Q=[t]Y-(I_{12}-W_2)=W_2-W_1.
$
The subtracted term is the contribution of its rank-two flats in the flat-lattice sum for $[t]Y$; palindromicity identifies $[t]Y$ with the penultimate coefficient.

In rank four, set $A=[t^4]Y_M$, $B=[t^3]Y_M$, and $C=[t^2]Y_M$. The formulas are
$
\begin{aligned}
A&=T-I_{23}-I_{13}+W_3-I_{12}+W_2+W_1-1,\\
B&=T-I_{13}-I_{12}+W_1,\\
C&=T-I_{12}+W_2-I_{13}.
\end{aligned}
$
For $A=u(0,1)$, apply the Möbius recurrence over the proper flats and sum the rank-three expression over the planes, the rank-two expression over the lines, and $1$ over the points, with alternating signs. For $B=\sum_p u(p,1)$, use the rank-three expression instead in each upper interval $[p,1]$. For $C$, let $s(L)$ be the number of points on the line $L$ and $h(L)$ the number of planes containing it. The only contributions are
$
\sum_{\text{lines }L}(s(L)-1)(h(L)-1)
+\sum_{\text{planes }H}
 \bigl(\#\{\text{lines in }H\}-\#\{\text{points in }H\}\bigr).
$
The line term uses the two rank-two intervals on either side of a line; the plane term uses the rank-three formula for $[t]Q$. The top-flat $Q$ has degree less than two and contributes nothing. Expanding the products counts $T-I_{12}-I_{23}+W_2$, while the plane sum is $I_{23}-I_{13}$, as required.

The coefficient list is therefore $(A,B,C,B,A)$, and the geometric quantities we need are
$
C-B=W_2-W_1,\qquad
(B-A)-(C-B)=I_{23}-2W_2-W_3+W_1+1=:\kappa(M).
$

## 3. At least as many lines as points

In a simple matroid of rank at least three, two distinct points determine a unique line. Every point lies on a line, and every line omits a point. Suppose there were fewer lines than points. To apply Hall's theorem, give each line the points not incident with it as its candidate set. A single line has a candidate; for any set of at least two distinct lines, the union of candidates contains all but at most one point, since two distinct lines cannot meet in two distinct points. Under the supposition this is at least the number of lines, so Hall's condition holds for every set of lines.

We get distinct points $p_L$ with $p_L\notin L$, one assigned to each line. Joining $p_L$ to different points on $L$ gives different lines through $p_L$: equality of two such joins would force their line to be $L$ by uniqueness. Hence $|L|\le \deg(p_L)$, where $\deg(p)$ is the number of lines through $p$. Sum over all lines. The left side counts all point–line incidences, but the right counts the incidences at just the assigned points. There is an unassigned point and its degree is positive, a contradiction. Thus $W_2\ge W_1$, giving $C\ge B$.

## 4. Rank-preserving deletion bounds the gap

Let $M$ be simple of rank four. Delete a point $e$ outside a fixed basis, so $N=M\setminus e$ still has rank four. Call a flat $F$ of $M$ *old* if
$\operatorname{cl}_M(F\setminus\{e\})=F$, and *new* otherwise.

The old flats correspond bijectively to the flats of $N$, by trace $F\mapsto F\setminus\{e\}$ and inverse $U\mapsto\operatorname{cl}_M(U)$; this follows from $\operatorname{cl}_N(U)=\operatorname{cl}_M(U)\setminus\{e\}$. This correspondence preserves ranks and inclusions in both directions. A new flat $F$ contains $e$, but $e$ is not in the closure of its trace. Since that closure lies within $F$, the trace itself is a flat of $M$ of rank $\operatorname{rk}F-1$. In particular, a new plane contains a unique old line: its trace is such a line, and the trace of any old line contained in that plane is contained in its trace, so closing the old line's trace keeps it inside that rank-two flat.

Let $l,p$ be the numbers of new lines and new planes. The changes in $W_1,W_2,W_3$ are $1,l,p$. Old-line/old-plane incidences are preserved, and old-line/new-plane incidences contribute exactly $p$. Every new line is in at least two planes: extend a basis of the line to a rank-four basis, then take the closures obtained by adjoining each of the two additional basis elements individually. Those rank-three closures are distinct by independence. Thus incidences whose line is new add at least $2l$. Combining these disjoint types,
$
\Delta I_{23}\ge p+2l,\qquad
\kappa(M)-\kappa(N)\ge (p+2l)-2l-p+1=1.
$

Repeat the deletion until only the fixed four-element basis remains. Its flat lattice is Boolean, with $W_1=4,W_2=6,W_3=4,I_{23}=12$, so $\kappa=1$ there. Each reinstated point increases $\kappa$ by at least one. Hence
$
\kappa(M)\ge W_1-3\ge1 .
$

## 5. Log-concavity and the low ranks

In rank four put $x=B-A$, $y=C-B$. We proved $A>0$, $y\ge0$, and $x-y=\kappa(M)\ge1$. In particular $A,B,C$ are positive and
$
B^2-AC=(A+x)^2-A(A+x+y)=A(x-y)+x^2\ge0.
$
The other distinct inequality is $C^2\ge B^2$, from $C\ge B>0$. Palindromicity covers the third triple.

In rank three the list is $(A,B,B,A)$ with $A=u(0,1)>0$ and $B-A=W_2-1\ge0$; the closure of two elements of a basis supplies a rank-two flat. Each interior inequality reduces to $AB\le B^2$. In rank two, writing $m=W_1\ge2$, the list is $(m-1,m,m-1)$. Ranks zero and one give $(1)$ and $(1,1)$. These lists are positive and log-concave. Degrees beyond the rank have coefficient zero, so triples crossing or beyond the end satisfy the asserted inequality as well.

## Prior work and scope

Gao, Ruan, and Xie's [Theorem 1.6](https://arxiv.org/html/2507.01332v1) already proves the sparse paving case, including its overlap with this result. [Gao, Li, and Xie](https://arxiv.org/abs/2601.17314) prove equivariant results for uniform and $q$-uniform matroids. The [Rethlas archival manuscript](https://github.com/frenzymath/Rethlas_results/blob/895e3d12ba02224c9d8ba8d52882184c77afc8af/AlgComb/MatroidKazhdanLusztig/inverse_z_unimodal.pdf), which credits Luis Ferroni's earlier solution and Elias Badalov's independent proof, concerns all-rank **unimodality**, not log-concavity. We make no priority claim for unimodality. The contribution here is a rank-four log-concavity proof for arbitrary finite matroids and its checked formalization. The registry's automated review is not human peer review.
