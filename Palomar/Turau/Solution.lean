module

public import Proofs.Amnesiac
public import Proofs.AmnesiacFamily

@[expose] public section

namespace ConjectureLab.TurauSubmission

/-- Exact negation of the inequality posed in Turau, arXiv:2002.10752v4, §8.
This is not the weaker proved bound in Theorem 4. -/
theorem conjecture_false : ¬ Flooding.TurauConjecture := Flooding.turau_false

/-- Explicit 24-vertex certificate, with physical rounds 1, 2 and 3
carrying 12, 24 and 26 messages and round 4 empty. -/
theorem concrete_counterexample :
    Flooding.symmetric Flooding.graph ∧ Flooding.loopless Flooding.graph ∧
    Flooding.connected Flooding.graph ∧ ¬ Flooding.bipartite Flooding.graph ∧
    Flooding.seed.Nodup ∧ Flooding.seed.length = 4 ∧
    (Flooding.messages Flooding.graph Flooding.seed 0).length = 12 ∧
    (Flooding.messages Flooding.graph Flooding.seed 1).length = 24 ∧
    (Flooding.messages Flooding.graph Flooding.seed 2).length = 26 ∧
    (Flooding.messages Flooding.graph Flooding.seed 3).length = 0 ∧
    ∃ t, Flooding.isFloodNumber Flooding.graph 4 t ∧
      Flooding.isRadius Flooding.graph 10 ∧ t ≤ 3 ∧ 4*t < 10+4-1 := by
  have hd : Flooding.seed.Nodup := by decide
  have hl : Flooding.seed.length = 4 := by decide
  obtain ⟨r₁,r₂,r₃,r₄⟩ := Flooding.round_counts
  obtain ⟨t,hf,hr,hbad⟩ := Flooding.finite_counterexample
  exact ⟨Flooding.graph_symm,Flooding.graph_loopless,Flooding.graph_connected,
    Flooding.graph_nonbip,hd,hl,r₁,r₂,r₃,r₄,
    t,hf,hr,hf.2 _ 3 ⟨hd,hl⟩ Flooding.termination,hbad⟩

/-- The chain of k six-vertex gadgets is a simple connected non-bipartite
counterexample for each k ≥ 4. The literal optimal k-seed time t is at
most 3; the exact radius is floor(5k/2). -/
theorem infinite_family (k : Nat) (hk : 4 ≤ k) :
    (∀ u v : FloodFamily.Vertex k, FloodFamily.adj u v → FloodFamily.adj v u) ∧
    (∀ u : FloodFamily.Vertex k, ¬ FloodFamily.adj u u) ∧
    (∀ u v : FloodFamily.Vertex k, ∃ l, FloodFamily.Walk u v l) ∧
    (¬ ∃ color : FloodFamily.Vertex k → Bool,
      ∀ u v, FloodFamily.adj u v → color u ≠ color v) ∧
    ∃ t, FloodFamily.isFloodNumber (k:=k) t ∧ FloodFamily.isRadius (k:=k) (5*k/2) ∧
      t ≤ 3 ∧ k*t < (5*k/2)+k-1 ∧ (5*k/2)+k-1-k*t ≥ k/2-1 := by
  obtain ⟨hs,hl,hc,hb,_,_,_⟩ := FloodFamily.family_counterexample k hk
  exact ⟨hs,hl,hc,hb,FloodFamily.refutes_turau_for_each k hk⟩

end ConjectureLab.TurauSubmission

#print axioms ConjectureLab.TurauSubmission.conjecture_false
#print axioms ConjectureLab.TurauSubmission.concrete_counterexample
#print axioms ConjectureLab.TurauSubmission.infinite_family
