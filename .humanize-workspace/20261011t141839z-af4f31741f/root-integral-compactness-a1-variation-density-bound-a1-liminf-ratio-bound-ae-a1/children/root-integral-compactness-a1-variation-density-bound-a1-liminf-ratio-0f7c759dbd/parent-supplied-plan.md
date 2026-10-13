# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.variation_density_bound-a1.liminf_ratio_bound_ae-a1.liminf_bound_ae_of_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-variation-density-bound-a1-liminf-ratio-0f7c759dbd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.variation_density_bound-a1.liminf_ratio_bound_ae-a1`
- Child key: `liminf_bound_ae_of_cover`
- Declaration: `Submission.intcpt_vdb_liminf_bound_ae_of_cover`
- Exact Lean type: `∀ (N C : ℕ) (μ : Measure (Euclidean N)) (ν : ℕ → Measure (Euclidean N)) (W : Set (Euclidean N)) (r : ℝ), (∀ (A : Set (Euclidean N)) (i : ℕ) (t : ℝ≥0∞), (∀ x ∈ A, ∃ σ : ℝ, 0 < σ ∧ σ < r ∧ μ (closedBall x σ) ≤ t * ν i (closedBall x σ)) → μ A ≤ (C : ℝ≥0∞) * t * ν i (thickening r A)) → ⨆ i, ν i (thickening r W) ≠ ∞ → ∀ᵐ x ∂μ, x ∈ W → ∃ c : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < r → liminf (fun i ↦ ν i (closedBall x ρ)) atTop ≤ (c : ℝ≥0∞) * μ (closedBall x ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
