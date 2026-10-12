# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af41ce05d4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1`
- Child key: `rellich_ball`
- Declaration: `Submission.dorag_ha_rellich_ball`
- Exact Lean type: `∀ (n : ℕ) (M : ℝ) (u : ℕ → Euclid n → ℝ), 0 < n → (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) 1, u j x ^ 2 ≤ M) → (∀ j, ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ M) → ∃ (φ : ℕ → ℕ) (W : Euclid n → ℝ), StrictMono φ ∧ MemLp W 2 (volume.restrict (ball (0 : Euclid n) 1)) ∧ Tendsto (fun j => ∫ x in ball (0 : Euclid n) 1, (u (φ j) x - W x) ^ 2) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
