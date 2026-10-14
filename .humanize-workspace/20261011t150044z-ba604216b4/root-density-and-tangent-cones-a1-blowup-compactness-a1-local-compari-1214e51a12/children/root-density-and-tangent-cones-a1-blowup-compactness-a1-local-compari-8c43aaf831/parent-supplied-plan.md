# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.cutoff_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8c43aaf831/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child key: `cutoff_gradient`
- Declaration: `Submission.dtc_bc_lc_sl_sf_cutoff_gradient`
- Exact Lean type: `∀ (P N : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (a b : ℝ), a < b → Continuous f → (∀ᵐ x ∂(μHE[N].restrict M), HasApproximateTangentSpaceAt N M x (approxTangentPlane N M x) ∧ G x ∈ approxTangentPlane N M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[N] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |f y - f x - inner ℝ (G x) (y - x)|}) / ENNReal.ofReal (r ^ N)) (𝓝[>] 0) (𝓝 0)) → (∀ᵐ x ∂(μHE[N].restrict M), f x = a → G x = 0) → (∀ᵐ x ∂(μHE[N].restrict M), f x = b → G x = 0) → ∀ᵐ x ∂(μHE[N].restrict M), HasApproximateTangentSpaceAt N M x (approxTangentPlane N M x) ∧ (if a < f x ∧ f x < b then -(b - a)⁻¹ • G x else 0) ∈ approxTangentPlane N M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[N] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |min 1 (max 0 ((b - f y) / (b - a))) - min 1 (max 0 ((b - f x) / (b - a))) - inner ℝ (if a < f x ∧ f x < b then -(b - a)⁻¹ • G x else 0) (y - x)|}) / ENNReal.ofReal (r ^ N)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
