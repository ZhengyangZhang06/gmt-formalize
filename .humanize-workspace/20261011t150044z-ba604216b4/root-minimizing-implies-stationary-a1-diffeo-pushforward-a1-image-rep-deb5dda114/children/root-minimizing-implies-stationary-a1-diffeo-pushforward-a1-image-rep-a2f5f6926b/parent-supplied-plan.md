# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1.image_measure_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-a2f5f6926b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1`
- Child key: `image_measure_comparison`
- Declaration: `Submission.dpfir_ii_map_restrict_image_le_smul`
- Exact Lean type: `∀ (P n : ℕ) (φ ψ : Euclid P → Euclid P) (Λ : NNReal) (S : Set (Euclid P)), LipschitzWith Λ φ → Measurable ψ → LeftInverse ψ φ → (μHE[n].restrict (φ '' S)).map ψ ≤ ((Λ : ℝ≥0∞) ^ n) • μHE[n].restrict S`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
