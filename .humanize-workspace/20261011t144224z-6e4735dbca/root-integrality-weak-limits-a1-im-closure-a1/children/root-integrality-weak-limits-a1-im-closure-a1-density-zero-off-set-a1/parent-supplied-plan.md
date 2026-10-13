# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1-density-zero-off-set-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.im_closure-a1`
- Child key: `density_zero_off_set`
- Declaration: `Submission.iwl_imc_density_zero_off_set`
- Exact Lean type: `∀ (P k : ℕ) (U S : Set (Eucl P)) (g : Eucl P → ℝ≥0∞), IsOpen U → NullMeasurableSet S (μHE[k] : Measure (Eucl P)) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∫⁻ y in S ∩ K, g y ∂(μHE[k] : Measure (Eucl P)) < ∞) → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ U → x ∉ S → ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * ∫⁻ y in S ∩ closedBall x (R * r), g y ∂(μHE[k] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.rectifiability-a1.density_comparison-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
