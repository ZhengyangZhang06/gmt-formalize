# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.null_off_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c27abc1fef/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child key: `null_off_image`
- Declaration: `Submission.cbr_ci_pw_density_null_off_image`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ) (A : Set (Euclid P)), IsOpen U → Continuous q → IntegrableOn u U → σ univ < ∞ → Integrable h σ → σ Aᶜ = 0 → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → volume (B ∩ {y | u y ≠ 0}) ≤ volume (B ∩ q '' A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
