# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1.const_eq_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-bba0184232/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1`
- Child key: `const_eq_zero`
- Declaration: `Submission.dtc_bc_cz_isMinimizingIn_const_eq_zero`
- Exact Lean type: `∀ (n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid n)) n) (c : ℝ), 0 < n → IsCompact X.support → (∀ ω : TestFormOn (univ : Set (Euclid n)) n, X ω = c * ∫ y, (ω : DifferentialForm (Euclid n) n) y ⇑(EuclideanSpace.basisFun (Fin n) ℝ)) → c = 0`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1.bump_form-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
