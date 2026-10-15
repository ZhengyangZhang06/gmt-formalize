# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_family-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-ea88c12991/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1`
- Child key: `cycle_slice_family`
- Declaration: `Submission.ind_pi_ss_cycle_slice_family`
- Exact Lean type: `SlicingTheorem → ∀ (P m : ℕ) (U W : Set (Eucl P)) (X : GeometricCurrentOn U (m + 1)) (d : Eucl P → ℝ) (L : ℝ≥0) (a b : ℝ), IsOpen U → CompactlyContainedOpen W U → LipschitzWith L d → a < b → X.boundary = 0 → (∀ V, CompactlyContainedOpen V U → X.massOn V < ∞) → ∃ (A : ℝ → GeometricCurrentOn U (m + 1)) (g : ℝ → ℝ≥0∞), Measurable g ∧ (∀ t, IsRestriction X {x | x ∈ U ∧ d x < t} (A t)) ∧ (∀ t ∈ Ioo a b, (A t).boundary.massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * X.massOn W`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_boundary-a1`
- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.restriction_mass_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
