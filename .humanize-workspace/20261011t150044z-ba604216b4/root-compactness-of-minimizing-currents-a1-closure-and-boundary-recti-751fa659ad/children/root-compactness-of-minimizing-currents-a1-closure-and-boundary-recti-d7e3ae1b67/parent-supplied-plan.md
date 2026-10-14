# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1.sum_planes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d7e3ae1b67/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1`
- Child key: `sum_planes`
- Declaration: `Submission.cbr_ci_cp_atm_sum_planes_of_carried`
- Exact Lean type: `∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)), Z.Countable → σ Zᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n]) → ν = Measure.sum (fun w : Z => σ {(w : Euclid P)} • (μHE[n]).restrict {y : Euclid P | y - w ∈ V})`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
