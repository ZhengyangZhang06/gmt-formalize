# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_boundary-a1.pullback_integral_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-e64ae346b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_boundary-a1`
- Child key: `pullback_integral_limit`
- Declaration: `Submission.dpf_pb_imrep_pullback_integral_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (U K' : Set (Euclid P)) (R : IMRep U n) (α : DifferentialForm (Euclid P) n) (ψ : ℕ → Euclid P → Euclid P) (φ : Euclid P → Euclid P) (C : ℝ), IsCompact K' → K' ⊆ U → Continuous α → HasCompactSupport α → tsupport α ⊆ U → (∀ k, ContDiff ℝ 1 (ψ k)) → (∀ k x, x ∉ K' → ψ k x = x) → (∀ k x, ‖fderiv ℝ (ψ k) x‖ ≤ C) → (∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (φ x))) → (∀ x, Tendsto (fun k => fderiv ℝ (ψ k) x) atTop (𝓝 (fderiv ℝ φ x))) → Tendsto (fun k => ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x)) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((α (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n]))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
