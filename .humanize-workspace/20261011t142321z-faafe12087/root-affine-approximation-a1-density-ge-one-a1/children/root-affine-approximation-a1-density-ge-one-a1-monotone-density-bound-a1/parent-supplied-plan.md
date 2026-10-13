# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.density_ge_one-a1.monotone_density_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-density-ge-one-a1-monotone-density-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.density_ge_one-a1`
- Child key: `monotone_density_bound`
- Declaration: `Submission.aal_dge1_density_le_monotone_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (x : Amb n ℓ) (ω R A β θ₀ : ℝ) (F : ℝ → ℝ), 0 < ω → 0 < R → 0 < β → 0 ≤ θ₀ → (∀ t : ℝ, 0 < t → t ≤ R → |F t - 1| ≤ A * (t / R) ^ β) → (∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R → F s * ((μ (closedBall x s)).toReal / s ^ n) + (F s - 1) ≤ F t * ((μ (closedBall x t)).toReal / t ^ n) + (F t - 1)) → Tendsto (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal (ω * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ₀)) → ∀ t : ℝ, 0 < t → t ≤ R → ω * θ₀ ≤ (1 + A * (t / R) ^ β) * ((μ (closedBall x t)).toReal / t ^ n) + A * (t / R) ^ β`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
