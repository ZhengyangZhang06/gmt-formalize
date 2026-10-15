# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.approx_grad_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-e39c8a92aa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `approx_grad_unique`
- Declaration: `Submission.dtc_bc_lc_sl_ll_approx_grad_unique`
- Exact Lean type: `∀ (P N : ℕ) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (h : Euclid P → ℝ) (u u' : Euclid P), HasApproximateTangentSpaceAt N A x Q → u ∈ Q → u' ∈ Q → (∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[N] (A ∩ ball x r ∩ {y | ε * ‖y - x‖ < |h y - h x - inner ℝ u (y - x)|}) / ENNReal.ofReal (r ^ N)) (𝓝[>] 0) (𝓝 0)) → (∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[N] (A ∩ ball x r ∩ {y | ε * ‖y - x‖ < |h y - h x - inner ℝ u' (y - x)|}) / ENNReal.ofReal (r ^ N)) (𝓝[>] 0) (𝓝 0)) → u = u'`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
