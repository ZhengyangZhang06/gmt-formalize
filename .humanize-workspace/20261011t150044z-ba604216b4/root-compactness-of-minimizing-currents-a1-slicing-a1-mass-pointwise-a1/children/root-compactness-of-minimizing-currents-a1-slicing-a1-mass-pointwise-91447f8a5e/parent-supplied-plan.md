# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.strip_lintegral_le-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-pointwise-91447f8a5e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1`
- Child key: `strip_lintegral_le`
- Declaration: `Submission.cmcs_smp_strip_lintegral_le`
- Exact Lean type: `∀ (P k : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (W S : Set (Euclid P)) (c : ℝ), (∀ x, ‖fderiv ℝ g x‖ ≤ c) → (∀ x, fderiv ℝ g x ≠ 0 → x ∈ S) → tsupport η ⊆ W → (∀ x, covectorEuclideanNorm (η x) ≤ 1) → ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ∂μ ≤ ENNReal.ofReal c * μ (W ∩ S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
