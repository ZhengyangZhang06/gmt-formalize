# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_sard-a1.chart_composition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1-chart-composition-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_sard-a1`
- Child key: `chart_composition`
- Declaration: `Submission.c1_sard_local_representation_comp`
- Exact Lean type: `∀ (n k N : ℕ) (M S : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (D : Set (Rn k)) (V₁ : Set (Rn n)) (l : Rn k → Rn n), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → S ⊆ M → V₁ ⊆ V → Chapter02.IsSimonLocalRepresentation 1 (ψ ⁻¹' S) D V₁ l → ∃ W₁ : Set (Rn N), W₁ ⊆ W ∧ ψ '' V₁ = W₁ ∩ M ∧ Chapter02.IsSimonLocalRepresentation 1 S D W₁ (ψ ∘ l)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
