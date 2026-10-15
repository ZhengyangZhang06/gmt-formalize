# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1.boundary_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-92759fcd01/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1`
- Child key: `boundary_zero`
- Declaration: `Submission.cbr_cipi_plane_boundary_zero`
- Exact Lean type: `∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P), Orthonormal ℝ v → ∀ φ : TestFormOn (univ : Set (Euclid P)) d, (∀ t : ℝ, ∫ y in (Submodule.span ℝ (Set.range v) : Set (Euclid P)) ∩ {y : Euclid P | inner ℝ y (v 0) < t}, exteriorDerivative (φ : DifferentialForm (Euclid P) d) y v ∂μHE[(d + 1)] = ∫ y in {y : Euclid P | y - t • v 0 ∈ Submodule.span ℝ (Set.range (Fin.tail v))}, (φ : DifferentialForm (Euclid P) d) y (Fin.tail v) ∂μHE[d]) → ∫ y in (Submodule.span ℝ (Set.range v) : Set (Euclid P)), exteriorDerivative (φ : DifferentialForm (Euclid P) d) y v ∂μHE[(d + 1)] = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
