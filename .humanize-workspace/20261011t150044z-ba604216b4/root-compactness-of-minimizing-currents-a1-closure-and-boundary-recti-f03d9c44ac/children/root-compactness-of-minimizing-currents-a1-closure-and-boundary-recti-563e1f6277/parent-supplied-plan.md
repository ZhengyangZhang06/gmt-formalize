# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-563e1f6277/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1`
- Child key: `uniform_density`
- Declaration: `Submission.cbrr_uniform_density_on_large_set`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), 0 < n → MeasurableSet M → μHE[n] M ≠ ∞ → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → ∀ (a b ε : ℝ), ENNReal.ofReal a < unitBallVolume n → 0 < b → 0 < ε → ∃ (E : Set (Euclid P)) (δ : ℝ), E ⊆ M ∧ 0 < δ ∧ μHE[n] (M \ E) < ENNReal.ofReal ε ∧ (∀ x ∈ E, Module.finrank ℝ (Q x) = n) ∧ (∀ y ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (a * ρ ^ n) ≤ (μHE[n].restrict M) (closedBall y ρ)) ∧ ∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → (μHE[n].restrict M) ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤ ENNReal.ofReal (b * ρ ^ n)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.tangent_lower_density-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1.lusin_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
