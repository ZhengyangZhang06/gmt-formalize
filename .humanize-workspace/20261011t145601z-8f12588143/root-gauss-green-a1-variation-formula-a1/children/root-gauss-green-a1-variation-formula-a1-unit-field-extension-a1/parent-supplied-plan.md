# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.variation_formula-a1.unit_field_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-variation-formula-a1-unit-field-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.variation_formula-a1`
- Child key: `unit_field_extension`
- Declaration: `Submission.gaussGreenVar_exists_unit_field_eqOn_compact`
- Exact Lean type: `∀ (N : ℕ) (C V : Set (Rn N)) (f : Rn N → Rn N), IsCompact C → IsOpen V → C ⊆ V → ContinuousOn f C → (∀ x ∈ C, ‖f x‖ ≤ 1) → ∃ g : Rn N → Rn N, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, ‖g x‖ ≤ 1) ∧ ∀ x ∈ C, g x = f x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
