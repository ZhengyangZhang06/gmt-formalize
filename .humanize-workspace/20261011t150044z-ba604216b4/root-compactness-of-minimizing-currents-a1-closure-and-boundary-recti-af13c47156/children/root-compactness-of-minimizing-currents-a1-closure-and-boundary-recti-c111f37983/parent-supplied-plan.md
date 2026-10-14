# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.rn_carrier-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c111f37983/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1`
- Child key: `rn_carrier`
- Declaration: `Submission.cbr_ci_dr_withDensity_carrier_of_absolutelyContinuous`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Euclid P)) (M₀ : Set (Euclid P)), μ univ < ∞ → MeasurableSet M₀ → ν M₀ < ∞ → μ M₀ᶜ = 0 → (∀ E : Set (Euclid P), ν E = 0 → μ E = 0) → ∃ (M : Set (Euclid P)) (θ : Euclid P → ℝ), MeasurableSet M ∧ M ⊆ M₀ ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ μ = (ν.restrict M).withDensity (fun x => ENNReal.ofReal (θ x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
