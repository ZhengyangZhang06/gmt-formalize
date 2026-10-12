# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1.zero_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-zero-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_completeness-a1`
- Child key: `zero_density`
- Declaration: `Submission.imc_ae_zero_density_off_set`
- Exact Lean type: `∀ (Q n : ℕ) (S : Set (Eucl Q)) (g : Eucl Q → ℝ≥0∞), NullMeasurableSet S (μHE[n] : Measure (Eucl Q)) → (∀ K : Set (Eucl Q), IsCompact K → ∫⁻ x in S ∩ K, g x ∂(μHE[n] : Measure (Eucl Q)) < ∞) → ∀ᵐ y ∂(μHE[n] : Measure (Eucl Q)), y ∉ S → Tendsto (fun ρ : ℝ => (∫⁻ x in S ∩ closedBall y ρ, g x ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
