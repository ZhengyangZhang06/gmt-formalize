# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-imrep-density-ae-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1`
- Child key: `imrep_density_ae`
- Declaration: `Submission.dimred_tr_imrep_density_ae`
- Exact Lean type: `∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (Set.indicator (R.carrier ∩ W) (fun y => (R.mult y : ℝ≥0∞)) x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
