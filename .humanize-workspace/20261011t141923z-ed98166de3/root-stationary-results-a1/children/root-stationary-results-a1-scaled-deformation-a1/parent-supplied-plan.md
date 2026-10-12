# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.scaled_deformation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-scaled-deformation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1`
- Child key: `scaled_deformation`
- Declaration: `Submission.scaled_field_deformation_is_admissible`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)) (Y : Rn N → Rn N), IsOpen U → ContDiff ℝ 2 Y → HasCompactSupport Y → tsupport Y ⊆ U → ∃ c : ℝ, 0 < c ∧ IsAdmissibleDeformation 2 U (tsupport Y) (fun t x ↦ x + (c * t) • Y x) ∧ ∀ x, initialVelocity (fun t x ↦ x + (c * t) • Y x) x = c • Y x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
