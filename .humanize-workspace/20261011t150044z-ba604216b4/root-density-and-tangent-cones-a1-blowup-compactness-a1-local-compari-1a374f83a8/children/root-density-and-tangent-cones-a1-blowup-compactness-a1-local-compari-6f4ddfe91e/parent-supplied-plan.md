# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.grad_weak_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-6f4ddfe91e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `grad_weak_limit`
- Declaration: `Submission.dtc_bc_lc_sl_ll_grad_weak_limit`
- Exact Lean type: `∀ (N : ℕ) (us : ℕ → Euclid N → ℝ) (u : Euclid N → ℝ) (Λ : NNReal) (W : Euclid N → Euclid N), (∀ k, LipschitzWith Λ (us k)) → LipschitzWith Λ u → TendstoUniformly us u atTop → Integrable W → Tendsto (fun k => ∫ y, fderiv ℝ (us k) y (W y)) atTop (𝓝 (∫ y, fderiv ℝ u y (W y)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
