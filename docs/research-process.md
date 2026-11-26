# Research process

Inspired by [the Davis–Astra conjecture catalog](https://github.com/1337isnot1337/solved-conjectures), this project keeps active searches separate from the public results table. Running more attempts is useful only if the results can be checked without trusting the solver.

1. **Intake.** Save the exact statement, a pinned primary source or version, the known cases, and a prior-resolution search. A catalog marked “open” can lag a proof or counterexample.
2. **Search in parallel, verify separately.** Give each attempt a fixed target and budget. Favor families that stress the assumptions. Use exact arithmetic for discrete witnesses. Save seeds, commands, finite coverage, failures and timeouts; separate them from theorem statements.
3. **Check the claim.** For a counterexample, independently check every hypothesis and the violated conclusion. For a proof, recompute the key identities and try to break the small cases and edge cases. Record which parts Lean, a certificate, or a separate reader actually checked.
4. **Publish only the reviewed scope.** Keep work-in-progress in scratch or a research branch. Promote a specific result note with source, proof or witness, replay and known limits, and update the README, catalogue and verification guide together. Never describe an exhausted search as a proof or a special case as the full problem.
5. **Close the loop.** Verify that the published result and checks match the intended commit. Share the link only once it is live.

See the [intake template](../templates/conjecture.md), [run log](../templates/run.md), and [verification guide](verification.md).
