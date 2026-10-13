# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.sup_net-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-3cd21fc12c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `sup_net`
- Declaration: `Submission.dorag_ha_rb_sup_net`
- Exact Lean type: `∀ (n : ℕ) (K : Set (Euclid n)) (g : ℕ → Euclid n → ℝ) (C : ℝ), IsCompact K → (∀ j, ∀ x ∈ K, |g j x| ≤ C) → (∀ j, ∀ x ∈ K, ∀ y ∈ K, |g j x - g j y| ≤ C * ‖x - y‖) → ∀ δ : ℝ, 0 < δ → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∀ x ∈ K, |g j x - g k x| ≤ δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
