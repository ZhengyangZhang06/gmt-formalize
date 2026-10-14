# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1.close_pair-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-44cb0ca038/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1`
- Child key: `close_pair`
- Declaration: `Submission.cmc_fc_cs_close_of_common_center`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P m : ℕ) (U : Set (Euclid P)) (Y Z Q S₁ S₂ : GeometricCurrentOn U (m + 1)) (R₁ R₂ : GeometricCurrentOn U (m + 2)), IsOpen U → IsIntegerMultiplicity R₁ → IsIntegerMultiplicity S₁ → IsIntegerMultiplicity R₂ → IsIntegerMultiplicity S₂ → Y - Q - S₁ = R₁.boundary → Z - Q - S₂ = R₂.boundary → ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ Y - Z - S = R.boundary ∧ R.mass + S.mass ≤ (R₁.mass + S₁.mass) + (R₂.mass + S₂.mass)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1.mass_sub_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
