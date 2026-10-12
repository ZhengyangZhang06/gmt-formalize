# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.mollifier_gradient-a1.smooth_duality_compact-a1.regularized_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1-smooth-duality-compact-a1-re-ee0a5bb0b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.mollifier_gradient-a1.smooth_duality_compact-a1`
- Child key: `regularized_field`
- Declaration: `Submission.bv_regularized_unit_field_admissible`
- Exact Lean type: `∀ (n : ℕ) (G : Rn n → Rn n) (χ : Rn n → ℝ) (η : ℝ) (g : Rn n → Rn n), ContDiff ℝ 1 G → ContDiff ℝ 1 χ → HasCompactSupport χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → 0 < η → (∀ x, g x = -(χ x / Real.sqrt (‖G x‖ ^ 2 + η ^ 2)) • G x) → ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ tsupport g ⊆ tsupport χ ∧ ∀ x, ‖g x‖ ≤ 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
