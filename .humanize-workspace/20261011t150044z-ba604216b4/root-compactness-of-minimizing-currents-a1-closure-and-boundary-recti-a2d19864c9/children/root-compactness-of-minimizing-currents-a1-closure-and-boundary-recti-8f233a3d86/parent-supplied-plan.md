# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1.halfspace_boundary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8f233a3d86/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1`
- Child key: `halfspace_boundary`
- Declaration: `Submission.cbr_cipi_plane_halfspace_boundary`
- Exact Lean type: `(∀ (P m : ℕ) (w : Fin m → Euclid P) (a : Euclid P), Orthonormal ℝ w → Measure.map (fun z : Fin m → ℝ => a + ∑ i, z i • w i) volume = (μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ IsClosed {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ (∀ K : Set (Euclid P), IsCompact K → ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) K < ∞) ∧ ∀ r : ℝ, 0 < r → 0 < ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) (ball a r)) → (∀ (d : ℕ) (g : (Fin (d + 1) → ℝ) → ℝ) (t : ℝ), ContDiff ℝ 1 g → HasCompactSupport g → (∀ i : Fin (d + 1), i ≠ 0 → ∫ z in {z : Fin (d + 1) → ℝ | z 0 < t}, fderiv ℝ g z (Pi.single i 1) = 0) ∧ ∫ z in {z : Fin (d + 1) → ℝ | z 0 < t}, fderiv ℝ g z (Pi.single 0 1) = ∫ z' : Fin d → ℝ, g (Fin.cons t z')) → ∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P), Orthonormal ℝ v → ∀ φ : TestFormOn (univ : Set (Euclid P)) d, ∀ t : ℝ, ∫ y in (Submodule.span ℝ (Set.range v) : Set (Euclid P)) ∩ {y : Euclid P | inner ℝ y (v 0) < t}, exteriorDerivative (φ : DifferentialForm (Euclid P) d) y v ∂μHE[(d + 1)] = ∫ y in {y : Euclid P | y - t • v 0 ∈ Submodule.span ℝ (Set.range (Fin.tail v))}, (φ : DifferentialForm (Euclid P) d) y (Fin.tail v) ∂μHE[d]`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1.extderiv_coords-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
