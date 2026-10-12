# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.monotonicity_density-a1.monotonicity_formula-a1.radial_first_variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-monotonicity-formula-a1-radial-first-var-2d6b5d3b85/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.monotonicity_density-a1.monotonicity_formula-a1`
- Child key: `radial_first_variation_bound`
- Declaration: `Submission.mono833_radial_first_variation_bound`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (ρ₀ Λ A t : ℝ) (φ : ℝ → ℝ), V.HasLocallyBoundedFirstVariation → ball x ρ₀ ⊆ U → 0 ≤ Λ → (∀ r : ℝ, 0 < r → r < ρ₀ → variationMeasure V (closedBall x r) ≤ ENNReal.ofReal Λ * V.weight (closedBall x r)) → ContDiff ℝ 1 φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, A ^ 2 ≤ s → φ s = 0) → 0 < A → 0 < t → t * A < ρ₀ → |V.firstVariation (fun y ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x))| ≤ A * Λ * t * ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂V.weight`

## Sibling prerequisites

- `root.monotonicity_density-a1.monotonicity_formula-a1.radial_layer_cake-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
