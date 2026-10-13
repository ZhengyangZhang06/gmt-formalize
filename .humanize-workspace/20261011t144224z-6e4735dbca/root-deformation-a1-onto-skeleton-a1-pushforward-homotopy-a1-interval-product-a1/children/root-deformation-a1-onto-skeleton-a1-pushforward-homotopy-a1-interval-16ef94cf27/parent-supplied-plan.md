# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.current_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-16ef94cf27/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child key: `current_criterion`
- Declaration: `Submission.dph_iprod_current_of_bound`
- Exact Lean type: `∀ (P q : ℕ) (U : Set (Eucl P)) (T₀ : TestFormOn U q →ₗ[ℝ] ℝ) (B : ℝ), 0 ≤ B → (∀ (ω : TestFormOn U q) (C : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) q) x) ≤ C) → |T₀ ω| ≤ B * C) → ∃ T : GeometricCurrentOn U q, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal B`

## Sibling prerequisites

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_norm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
