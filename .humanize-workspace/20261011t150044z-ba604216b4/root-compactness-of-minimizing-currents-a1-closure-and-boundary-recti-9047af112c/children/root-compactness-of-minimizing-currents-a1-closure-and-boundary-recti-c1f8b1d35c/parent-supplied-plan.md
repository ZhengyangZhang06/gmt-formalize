# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1.monotone_majorant-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c1f8b1d35c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1`
- Child key: `monotone_majorant`
- Declaration: `Submission.cbr_smm_monotone_majorant`
- Exact Lean type: `∀ (F : ℕ → ℝ → ℝ) (Z : ℕ → ℝ → ℝ≥0∞) (a b : ℝ) (L : NNReal), (∀ j, Monotone (F j)) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F j t - F j (t - h))) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (F j b - F j a)) atTop`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1.lintegral_deriv-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1.left_slope-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
