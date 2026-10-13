# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-772be56655/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child key: `coarea`
- Declaration: `Submission.dtc_bc_lc_sl_coarea`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal), MeasurableSet M → CountablyRectifiable (n + 1) M → (∀ K : Set (Euclid P), IsCompact K → μHE[n + 1] (M ∩ K) ≠ ∞) → LipschitzWith L f → ∃ G : Euclid P → Euclid P, Measurable G ∧ (∀ x, ‖G x‖ ≤ L) ∧ (∀ᵐ x ∂(μHE[n + 1].restrict M), HasApproximateTangentSpaceAt (n + 1) M x (approxTangentPlane (n + 1) M x) ∧ G x ∈ approxTangentPlane (n + 1) M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[n + 1] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |f y - f x - inner ℝ (G x) (y - x)|}) / ENNReal.ofReal (r ^ (n + 1))) (𝓝[>] 0) (𝓝 0)) ∧ (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) ∧ ∀ᵐ t, CountablyRectifiable n (M ∩ f ⁻¹' {t}) ∧ ∀ᵐ x ∂(μHE[n].restrict (M ∩ f ⁻¹' {t})), G x ≠ 0 ∧ HasApproximateTangentSpaceAt n (M ∩ f ⁻¹' {t}) x (approxTangentPlane (n + 1) M x ⊓ (ℝ ∙ G x)ᗮ)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.eilenberg-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
