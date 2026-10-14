# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1`
- Child key: `rectifiable_density_one`
- Declaration: `Submission.codim1_rdo_rectifiable_ae_density_one`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)), 1 ≤ n → MeasurableSet M → CountablyRectifiable n M → μHE[n] M ≠ ∞ → ∀ᵐ w ∂(μHE[n].restrict M), Tendsto (fun t : ℝ => μHE[n] (M ∩ ball w t) / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
