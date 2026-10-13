# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1.set_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-4564635bc9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1`
- Child key: `set_mass`
- Declaration: `Submission.cbr_ci_bl_db_withDensity_le`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (M B B' : Set (Euclid P)) (θ : Euclid P → ℝ) (g : Euclid P → ℝ≥0∞) (c K : ℝ≥0∞), MeasurableSet M → MeasurableSet B → B ⊆ B' → K ≠ ∞ → μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, ENNReal.ofReal (θ x) ≤ c + K * g x) → μ B ≤ c * μHE[n] (M ∩ B) + K * ∫⁻ x in M ∩ B', g x ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
