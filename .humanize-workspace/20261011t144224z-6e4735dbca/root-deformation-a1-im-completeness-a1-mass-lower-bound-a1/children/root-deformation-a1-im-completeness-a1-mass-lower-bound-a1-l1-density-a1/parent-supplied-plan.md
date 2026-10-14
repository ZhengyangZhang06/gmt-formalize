# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.l1_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1-l1-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1`
- Child key: `l1_density`
- Declaration: `Submission.imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le`
- Exact Lean type: `∀ (N : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure (Eucl N)) [IsFiniteMeasure ν] (f : Eucl N → E), MemLp f 1 ν → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ g : Eucl N → E, HasCompactSupport g ∧ eLpNorm (f - g) 1 ν ≤ ε ∧ Continuous g ∧ MemLp g 1 ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
