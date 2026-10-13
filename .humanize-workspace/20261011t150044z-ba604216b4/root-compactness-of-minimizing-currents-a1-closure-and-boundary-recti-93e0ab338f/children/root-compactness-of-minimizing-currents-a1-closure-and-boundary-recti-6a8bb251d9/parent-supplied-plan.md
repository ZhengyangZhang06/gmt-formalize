# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6a8bb251d9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1`
- Child key: `plane_measure`
- Declaration: `Submission.cbr_cipi_affine_plane_measure`
- Exact Lean type: `∀ (P m : ℕ) (w : Fin m → Euclid P) (a : Euclid P), Orthonormal ℝ w → Measure.map (fun z : Fin m → ℝ => a + ∑ i, z i • w i) volume = (μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ IsClosed {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ (∀ K : Set (Euclid P), IsCompact K → ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) K < ∞) ∧ ∀ r : ℝ, 0 < r → 0 < ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) (ball a r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
