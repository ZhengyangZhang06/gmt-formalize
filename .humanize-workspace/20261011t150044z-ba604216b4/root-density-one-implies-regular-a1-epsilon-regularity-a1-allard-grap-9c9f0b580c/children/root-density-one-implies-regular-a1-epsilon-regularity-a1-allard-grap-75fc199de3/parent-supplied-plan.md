# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.l2_pairing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-75fc199de3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1`
- Child key: `l2_pairing`
- Declaration: `Submission.dorag_haa_l2_pairing_tendsto`
- Exact Lean type: `∀ (n : ℕ) (R : ℝ) (f : ℕ → Euclid n → ℝ) (W g : Euclid n → ℝ), (∀ j, MemLp (f j) 2 (volume.restrict (ball (0 : Euclid n) R))) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → MemLp g 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (f j x - W x) ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, f j x * g x) atTop (𝓝 (∫ x in ball (0 : Euclid n) R, W x * g x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
