# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d692d7eef5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1`
- Child key: `cone_density`
- Declaration: `Submission.cbrr_tangent_cone_density_zero`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → μHE[n] M ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → ∀ t : ℝ≥0∞, 0 < t → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (M ∩ ({z | 2 * ‖Q.starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ)) ≤ t * ENNReal.ofReal (ρ ^ n)`

## Sibling prerequisites

- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1.blowup_image_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
