# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1.point_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1-po-5decd78813/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1`
- Child key: `point_current`
- Declaration: `Submission.dor_zdm_point_current`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (ξ₀ : MultiVector P n), IsOpen U → x ∈ U → (∃ D : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, D ω = ξ₀ ((ω : DifferentialForm (Euclid P) n) x)) ∧ ∀ D : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, D ω = ξ₀ ((ω : DifferentialForm (Euclid P) n) x)) → ξ₀ ≠ 0 → D.support = {x}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
