# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.span_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-acb6377c81/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Child key: `span_orientation`
- Declaration: `Submission.cmcdt_lpi_unit_orientation_span`
- Exact Lean type: `∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → 0 < Matrix.det (Matrix.of fun a b => inner ℝ (v a) (v b)) ∧ Real.sqrt (Matrix.det (Matrix.of fun a b => inner ℝ (v a) (v b))) ≤ ∏ a, ‖v a‖ ∧ ∃ ξ : MultiVector P n, IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range v)) ∧ (∀ α : Covector (Euclid P) n, α v = Real.sqrt (Matrix.det (Matrix.of fun a b => inner ℝ (v a) (v b))) * ξ α) ∧ ∀ ζ : MultiVector P n, IsUnitOrientationOf ζ (Submodule.span ℝ (Set.range v)) → ζ = ξ ∨ ζ = -ξ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
