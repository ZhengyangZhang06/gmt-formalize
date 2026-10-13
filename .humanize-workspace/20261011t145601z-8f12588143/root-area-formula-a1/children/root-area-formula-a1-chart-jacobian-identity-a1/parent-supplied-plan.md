# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.area_formula-a1.chart_jacobian_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-area-formula-a1-chart-jacobian-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.area_formula-a1`
- Child key: `chart_jacobian_identity`
- Declaration: `Submission.areaFormula_chart_jacobian_identity`
- Exact Lean type: `∀ (n N p : ℕ) (M : Set (Rn N)) (θ : Rn N → ℝ) (f : Rn N → Rn p) (ψ : Rn n → Rn N) (u : Rn n), θ (ψ u) ≠ 0 → HasWeightedApproximateTangentSpaceAt n M θ (ψ u) (LinearMap.range (fderiv ℝ ψ u).toLinearMap) → (∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)) → approxTangentPlane n M θ (ψ u) = LinearMap.range (fderiv ℝ ψ u).toLinearMap ∧ (∃ L : ↥(LinearMap.range (fderiv ℝ ψ u).toLinearMap) →L[ℝ] Rn p, HasTangentialDifferentialAt (LinearMap.range (fderiv ℝ ψ u).toLinearMap) f (ψ u) L) ∧ areaJacobian (approxTangentPlane n M θ (ψ u)) f (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet = (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
