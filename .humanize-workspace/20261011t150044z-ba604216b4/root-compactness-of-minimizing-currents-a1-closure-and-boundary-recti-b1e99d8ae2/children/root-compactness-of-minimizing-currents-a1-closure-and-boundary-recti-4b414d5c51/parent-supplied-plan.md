# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.steiner_volume-a1.cavalieri_coordinate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-4b414d5c51/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.steiner_volume-a1`
- Child key: `cavalieri_coordinate`
- Declaration: `Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq`
- Exact Lean type: `∀ (d : ℕ) (j : Fin d) (S A : Set (Euclid d)), MeasurableSet S → MeasurableSet A → (∀ y : Euclid d, volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ S} = volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}) → volume S = volume A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
