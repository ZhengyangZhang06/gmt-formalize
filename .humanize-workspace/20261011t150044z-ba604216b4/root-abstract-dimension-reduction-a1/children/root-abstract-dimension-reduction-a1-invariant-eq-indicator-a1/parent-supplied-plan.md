# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.invariant_eq_indicator-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-invariant-eq-indicator-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1`
- Child key: `invariant_eq_indicator`
- Declaration: `Submission.adr_invariant_eq_indicator`
- Exact Lean type: `∀ (P n Q : ℕ) (ψ : Euclid P → Euclid Q) (L : Submodule ℝ (Euclid P)), LocallyIntegrable ψ μH[(n : ℝ)] → n ≤ Module.finrank ℝ L → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → ∃ L' : Submodule ℝ (Euclid P), Module.finrank ℝ L' = n ∧ ψ = Set.indicator (L' : Set (Euclid P)) (fun _ => ψ 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
