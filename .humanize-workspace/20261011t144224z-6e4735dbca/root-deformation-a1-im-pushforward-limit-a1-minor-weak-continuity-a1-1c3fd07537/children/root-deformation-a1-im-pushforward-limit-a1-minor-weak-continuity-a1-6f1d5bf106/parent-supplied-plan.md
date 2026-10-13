# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.det_dominated_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-6f1d5bf106/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1`
- Child key: `det_dominated_convergence`
- Declaration: `Submission.deformation_ipl_mwc_mil_tendsto_integral_mul_det`
- Exact Lean type: `∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (n : ℕ) (C : ℝ) (A : ℕ → Fin n → Fin n → α → ℝ) (A₀ : Fin n → Fin n → α → ℝ) (h : ℕ → α → ℝ) (h₀ H : α → ℝ), (∀ m t s, AEStronglyMeasurable (A m t s) μ) → (∀ m, AEStronglyMeasurable (h m) μ) → Integrable H μ → (∀ m t s x, |A m t s x| ≤ C) → (∀ᶠ m in atTop, ∀ x, |h m x| ≤ H x) → (∀ᵐ x ∂μ, Tendsto (fun m => h m x) atTop (𝓝 (h₀ x))) → (∀ᵐ x ∂μ, ∀ t s, Tendsto (fun m => A m t s x) atTop (𝓝 (A₀ t s x))) → Tendsto (fun m => ∫ x, h m x * Matrix.det (Matrix.of fun t s => A m t s x) ∂μ) atTop (𝓝 (∫ x, h₀ x * Matrix.det (Matrix.of fun t s => A₀ t s x) ∂μ))`

## Sibling prerequisites

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.abs_det_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
