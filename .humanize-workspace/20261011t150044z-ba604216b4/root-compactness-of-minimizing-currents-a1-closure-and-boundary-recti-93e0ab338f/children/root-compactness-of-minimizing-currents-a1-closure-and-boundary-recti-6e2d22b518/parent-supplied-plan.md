# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.weight_nat-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6e2d22b518/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1`
- Child key: `weight_nat`
- Declaration: `Submission.cbr_cipi_imrep_weight_const_nat`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (R : IMRep U m) (S : Set (Euclid P)) (c : ℝ), 0 < c → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → ((μHE[m] : Measure (Euclid P)).restrict S) K < ∞) → (∃ (x : Euclid P) (r : ℝ), 0 < ((μHE[m] : Measure (Euclid P)).restrict S) (ball x r)) → (∀ G : Set (Euclid P), IsOpen G → R.measure G = ENNReal.ofReal c * ((μHE[m] : Measure (Euclid P)).restrict S) G) → ∃ k : ℕ, c = k`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
