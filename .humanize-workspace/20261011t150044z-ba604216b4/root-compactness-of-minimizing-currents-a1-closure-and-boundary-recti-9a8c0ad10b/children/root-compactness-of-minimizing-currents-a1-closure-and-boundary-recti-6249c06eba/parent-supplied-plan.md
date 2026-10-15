# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.imrep_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6249c06eba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1`
- Child key: `imrep_measure`
- Declaration: `Submission.cbr_imRep_measure_basic`
- Exact Lean type: `∀ (P k : ℕ) (W : Set (Euclid P)) (R : IMRep W k), R.measure ≪ μHE[k].restrict R.carrier ∧ μHE[k].restrict R.carrier ≪ R.measure ∧ (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ x in R.carrier ∩ A, (R.mult x : ℝ≥0∞) ∂μHE[k]) ∧ R.measure R.carrierᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → R.measure K < ∞) ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ ω : DifferentialForm (Euclid P) k, R.action ω = ∫ x, R.orient x (ω x) ∂R.measure`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
