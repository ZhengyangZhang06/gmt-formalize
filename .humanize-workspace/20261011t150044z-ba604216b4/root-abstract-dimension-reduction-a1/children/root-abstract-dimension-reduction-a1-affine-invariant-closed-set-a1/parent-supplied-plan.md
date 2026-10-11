# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.affine_invariant_closed_set-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-affine-invariant-closed-set-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1`
- Child key: `affine_invariant_closed_set`
- Declaration: `Submission.adr_affine_invariant_closed_set`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)) (L : Submodule ℝ (Euclid P)), IsClosed S → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => y + lam • x) ⁻¹' S = S) → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ z, y + lam • z ∈ S ↔ z ∈ S) ∧ (S.Nonempty → (L : Set (Euclid P)) ⊆ S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
