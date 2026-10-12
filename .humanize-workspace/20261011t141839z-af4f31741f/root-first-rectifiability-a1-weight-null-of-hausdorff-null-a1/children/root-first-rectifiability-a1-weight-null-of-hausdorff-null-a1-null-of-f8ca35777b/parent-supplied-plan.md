# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1.null_of_ball_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-null-of-hausdorff-null-a1-null-of-f8ca35777b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1`
- Child key: `null_of_ball_bound`
- Declaration: `Submission.frt_measure_null_of_hausdorff_null_ball_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (A : Set (Euclidean N)) (c : ℝ≥0∞) (δ : ℝ), c ≠ ∞ → 0 < δ → μHE[n] A = 0 → (∀ x ∈ A, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → μ (closedBall x ρ) ≤ c * ENNReal.ofReal ρ ^ n) → μ A = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
