# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1.radial_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-d047613fa5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Child key: `radial_tendsto`
- Declaration: `Submission.allard52_amcl_radial_cutoff_tendsto`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ) (R t : ℝ), 0 < t → t < R → IntegrableOn f (closedBall y R) μ → (∀ k, Continuous (φ k)) → (∀ k u, 0 ≤ φ k u ∧ φ k u ≤ 1) → (∀ k u, u ≤ 1 → φ k u = 1) → (∀ k u, 1 + ε k ≤ u → φ k u = 0) → Tendsto ε atTop (𝓝 0) → Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * f x ∂μ) atTop (𝓝 (∫ x in closedBall y t, f x ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
