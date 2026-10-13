# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1`
- Child key: `slice_mass_bound`
- Declaration: `Submission.slicing_mass_bound`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ S : ℝ → GeometricCurrentOn U m, (∀ t, IsSlice T f t (S t)) → ∀ W, IsOpen W → W ⊆ U → ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) → ∀ a b : ℝ, a < b → ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W`

## Sibling prerequisites

- `root.slicing-a1.mass_representation-a1`
- `root.slicing-a1.representation_unique-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
