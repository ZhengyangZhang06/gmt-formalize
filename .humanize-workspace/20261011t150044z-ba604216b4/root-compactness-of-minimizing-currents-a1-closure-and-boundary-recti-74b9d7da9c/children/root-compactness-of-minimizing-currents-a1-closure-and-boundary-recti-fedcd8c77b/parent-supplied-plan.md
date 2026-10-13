# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_limit-a1.riesz_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-fedcd8c77b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_limit-a1`
- Child key: `riesz_open`
- Declaration: `Submission.cbr_vl_riesz_measure_on_open`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (Λ : (Euclid P → ℝ) → ℝ), IsOpen U → (∀ f g : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (f + g) = Λ f + Λ g) → (∀ (c : ℝ) (f : Euclid P → ℝ), Continuous f → HasCompactSupport f → tsupport f ⊆ U → Λ (c • f) = c * Λ f) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → (∀ x, 0 ≤ f x) → 0 ≤ Λ f) → ∃ μ : Measure (Euclid P), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∫ x, f x ∂μ = Λ f`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
