# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.isoperimetric-a1.lattice_mass_lower_bound-a1.box_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-lattice-mass-lower-bound-a1-box-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1`
- Child key: `box_measure`
- Declaration: `Submission.isoperimetric_coord_box_measure`
- Exact Lean type: `∀ (n N : ℕ) (α : SimonMultiIndex n N) (c : Fin N → ℝ) (a b : ℝ), a ≤ b → (μHE[n] : Measure (Eucl N)) {x : Eucl N | ∀ i : Fin N, (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧ (i ∉ range α → x i = c i)} = ENNReal.ofReal ((b - a) ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
