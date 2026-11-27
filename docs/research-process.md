# Research and publication policy

1. Pin the primary statement and version, including every hypothesis. Record exact computations and incomplete arguments privately, not as public results.
2. Search for prior resolutions before working and again before publishing. Check primary literature, updated preprints, reference chains, problem databases, Lean repositories, and issue threads. Search alternate names and mathematically equivalent statements. Record the date and what sources were checked.
3. Cite and credit prior results, including independently rediscovered ones. A new proof of a known theorem must say what is new about the proof, not claim the theorem was open. If priority remains unclear, say so; a search cannot prove that no proof exists.
4. Machine-check the **exact public statement** in Lean, without `sorry`, custom axioms, or trust shortcuts. A finite witness or a conditional lemma does not justify publishing a general claim. A separate reviewer must compare the theorem declaration to the prose and source hypotheses.
5. Register each approved result with its Lean declarations and source audit, then run the publication gate. Publish only the reviewed scope. Keep draft branches local or private. The [Davis–Astra catalogue](https://github.com/1337isnot1337/solved-conjectures) inspired the research/publication separation.

## Publish a result

1. Add a directory under `results/` and a matching entry in the [publication registry](../results/registry.json). Choose a result kind that describes what the proof settles. The separate `disposition` field records the prior-work finding.
2. For a research result, point `landing` to its README. Lead with the claim, hypotheses and scope. Set `proof` to the written proof’s filename. Link that file, the Lean source, `audit.md` and [reproduction instructions](verification.md). Name every registered Lean declaration. For a known baseline, the audit can serve as its landing page.
3. Import the proof through the default `Proofs` target. Regenerate the catalogue with `python3 scripts/check_publication.py --write-catalogue --metadata-only`, then run the [full verification](verification.md). Commit the registry, both generated views and the result files together.
4. Once Palomar publishes a result, confirm its title, author, version, source commit and registration date against its public record. Add its versioned entry link to the [registration list](palomar-registrations.md) and any corresponding result page. Update the [filing queue](palomar-queue.md) when the commit and project path match. A registration can refer to a proof on another commit.
