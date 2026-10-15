# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.uniform_lipschitz_near_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-un-f5c04592aa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1`
- Child key: `uniform_lipschitz_near_compact`
- Declaration: `Submission.lpf_tde_uniform_lipschitz_near_compact`
- Exact Lean type: `∀ (P Q : ℕ) (U K : Set (Eucl P)) (f : Eucl P → Eucl Q), IsOpen U → LocallyLipschitzOn U f → IsCompact K → K ⊆ U → ∃ (C : ℝ≥0) (ρ : ℝ), 0 < ρ ∧ ∀ x ∈ K, ball x ρ ⊆ U ∧ LipschitzOnWith C f (ball x ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
