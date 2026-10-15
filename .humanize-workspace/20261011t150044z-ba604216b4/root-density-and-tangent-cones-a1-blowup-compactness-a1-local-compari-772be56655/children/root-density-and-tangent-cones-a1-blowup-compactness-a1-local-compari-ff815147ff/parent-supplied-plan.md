# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.density_gradient_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-ff815147ff/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child key: `density_gradient_bound`
- Declaration: `Submission.dtc_bc_lc_sl_co_density_gradient_bound`
- Exact Lean type: `∀ (d P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (Y : Set (Euclid d)) (y : Euclid d), LipschitzWith L f → y ∈ Y → DifferentiableAt ℝ ψ y → DifferentiableAt ℝ F y → (∀ z ∈ Y, f (ψ z) = F z) → Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ e : Euclid d, |fderiv ℝ F y e| ≤ L * ‖fderiv ℝ ψ y e‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
