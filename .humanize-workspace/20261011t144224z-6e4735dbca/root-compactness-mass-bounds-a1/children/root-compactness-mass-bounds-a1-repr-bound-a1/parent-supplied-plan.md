# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_mass_bounds-a1.repr_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_mass_bounds-a1`
- Child key: `repr_bound`
- Declaration: `Submission.cmb_measureRepresentation_continuous_bound`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Eucl P)), CompactlyContainedOpen W U → ∀ (T : GeometricCurrentOn U n) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → ∀ (B C : ℝ), 0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → tsupport ω ⊆ W → (∀ x, covectorEuclideanNorm (ω x) ≤ C) → Integrable (fun x => v x (ω x)) μ ∧ |∫ x, v x (ω x) ∂μ| ≤ B * C`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.mass_bound-a1`
- `root.compactness_mass_bounds-a1.mollify-a1`
- `root.compactness_mass_bounds-a1.covector_expansion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
