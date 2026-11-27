# Projective inverse Z-polynomials: verification target

This is a scoped positive theorem for line-preserving represented matroids over finite fields. It does not prove log-concavity for all matroids. The statement asserts coefficient positivity through the matroid rank and strict log-concavity at interior indices. The solution proves agreement between the standalone Challenge recurrence and the main proof's definition. See `formalization.yaml` for scope and mathematical sources.

`Challenge.lean` contains the statement only; `Solution.lean` contains the checked proof. The pinned GitHub Actions run checks the exact snapshot with Palomar's full workflow before any registry submission.
