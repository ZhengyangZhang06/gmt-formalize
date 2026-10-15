# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1.comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a26c93c3da/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1`
- Child key: `comparison`
- Declaration: `Submission.cbrld_ns_eval_le_of_small_filling`
- Exact Lean type: `∀ (P d : ℕ) (A S : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (ω : TestFormOn (univ : Set (Euclid P)) (d + 1)) (m : ℝ≥0∞) (x : Euclid P) (c κ R : ℝ), 0 ≤ c → 0 ≤ κ → 0 < R → m < ∞ → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (d + 1)) y) ≤ 1) → (∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (x₀ : Euclid P) (ϱ : ℝ), 0 < ϱ → X.boundary = 0 → X.mass < ∞ → X.support ⊆ closedBall x₀ ϱ → |X ω| ≤ c * ϱ * X.mass.toReal) → S.boundary = A.boundary → A.mass ≤ m → S.mass ≤ ENNReal.ofReal κ * m → A.support ⊆ closedBall x R → S.support ⊆ closedBall x R → A ω ≤ (κ + c * R * (1 + κ)) * m.toReal`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1.support_sub-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1.mass_sub-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
