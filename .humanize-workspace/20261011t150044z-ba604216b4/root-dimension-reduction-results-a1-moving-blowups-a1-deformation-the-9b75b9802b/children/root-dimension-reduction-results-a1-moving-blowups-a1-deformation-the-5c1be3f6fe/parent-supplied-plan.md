# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.dyadic_series-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-5c1be3f6fe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1`
- Child key: `dyadic_series`
- Declaration: `Submission.dimred_mbl_dtsd_dyadic_series_bounds`
- Exact Lean type: `∀ (c₄ : NNReal) (Λ : ℕ → NNReal), (∀ j, (Λ j : ℝ) ≤ c₄ * 2 ^ j) → (∀ (C : NNReal) (A : ℝ≥0∞) (p q : ℕ) (a : ℕ → ℝ≥0∞), p ≤ q → a 0 ≤ A → (∀ j, a (j + 1) ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (q + 1))) * A) → ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ p * a j ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * (1 + C) * A) ∧ (∀ (K A : ℝ≥0∞) (p : ℕ) (z : ℕ → ℝ≥0∞), K ≠ ∞ → A ≠ ∞ → (∀ j, z j ≤ K * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (p + 1))) * A) → Tendsto (fun j => (2 * (Λ j : ℝ≥0∞)) ^ p * z j) atTop (𝓝 0))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
