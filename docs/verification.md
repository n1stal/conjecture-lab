# Verification

The commands below run from the repository root. Python 3.10+ and a C++17 compiler are enough for the exact computational results; a pinned Lean toolchain is used for the finite witness formalizations. NumPy and SciPy are only needed for the separately labeled exploratory spectral scripts.

## Six-vertex spectral polygon

```sh
workdir="$(mktemp -d)"
g++ -std=c++17 -O3 -Wall -Wextra experiments/chebotarev_exact6.cpp -o "$workdir/exact6"
"$workdir/exact6" > "$workdir/polys.txt"
python experiments/chebotarev_verify6.py < "$workdir/polys.txt"
python experiments/chebotarev_verify6_polygon.py < "$workdir/polys.txt"
rm -r "$workdir"
```

Expect 4,241,864 representatives and 44,729 distinct quotient characteristic polynomials. The two verifiers check the horizontal strip and all slanted supporting inequalities using exact integer arithmetic. The [technical note](../problems/chebotarev-q2.md) proves why enumeration covers the unweighted class and why the coefficient tests are equivalent to the spectral inequalities. This is a replayable computational result, not a Lean formalization or independent software reproduction.

## Erdős #982: convex octagons

```sh
python experiments/erdos_982_grid.py --side 10 --lattice square
python experiments/erdos_982_grid.py --side 10 --lattice triangular
```

Both outputs should end in `None` for the witness. The square case has 1,055 surviving depth-five prefixes and zero depth-six prefixes; the triangular case has 13,901 and 64 respectively, and zero depth-seven prefixes. These are traversal counts, not counts of geometric isomorphism classes. The centrally symmetric case is a [separate written proof](../problems/erdos-982.md#extension-central-symmetry-alone), not a consequence of either lattice run.

## Property P: reciprocal sums

```sh
python -m unittest discover -s tests -v
python verify.py results/*.json
python verify.py --replay results/exact-n200.json results/exact-n300.json results/exact-n150-without-one.json
python lab.py --mode exact --n 16 --output runs/oracle.json
python verify.py --brute-force runs/oracle.json
```

`verify.py` checks the witness against the original forbidden-triple condition and recomputes its exact reciprocal sum. With `--replay` it reruns the same exact algorithm; with `--brute-force` it verifies small instances through a separate direct enumerator. Only a completed exact run can establish finite optimality. The [raw report index](../results/README.md) states which runs were capped.

Lean source: [PropertyP.lean](../Proofs/PropertyP.lean). With [elan](https://lean-lang.org/install/) installed, use the repository's pinned toolchain and run `lake build --wfail`. The theorems are intended only to check witness validity and concrete integer-weight identities. A passing hosted or local Lean build was not established in the environment where the initial results were checked.

## Evidence labels

- **Exact computation:** exhaustive within the explicit finite class, with exact arithmetic and replay instructions. It does not imply the problem over an infinite domain is solved.
- **Written proof:** an argument for the exact stated scope. **AI-reviewed** means a separate AI pass reviewed it, not expert refereeing or formal verification.
- **Exploratory:** sampling, floating-point scouting or interrupted enumeration. Failure to find a witness is not a bound.
- **Lean source / verified:** source code is not a verification receipt. A result should be described as Lean-verified only after building the exact theorem and auditing its assumptions.

## Inverse Z-polynomials

Replay the binary census with `python experiments/inverse_z_binary.py --rank4-all`. This checks the coefficient formula in a finite family; the [written proof](../problems/inverse-z-rank-four.md) is what covers all matroids through rank four.
