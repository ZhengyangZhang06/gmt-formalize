# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.structure_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-structure-projection-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1`
- Child key: `structure_projection`
- Declaration: `Submission.rectifiability_structure_projection`
- Exact Lean type: `∀ (P m : ℕ) (A : Set (Eucl P)), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) A → (∃ S : ℕ → Set (Eucl P), A ⊆ ⋃ j, S j ∧ ∀ j, (μHE[m + 1] : Measure (Eucl P)) (S j) < ∞) → ∃ Q : Eucl P ≃ₗᵢ[ℝ] Eucl P, ∀ α : SimonMultiIndex (m + 1) P, (volume : Measure (Eucl (m + 1))) ((fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1))) '' A) = 0`

## Sibling prerequisites

- `root.rectifiability-a1.bf_projection_null_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
