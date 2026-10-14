# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.action_translation_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-inv-de5919aa84/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1`
- Child key: `action_translation_invariance`
- Declaration: `Submission.dimred_cs_ti_action_translation_invariant`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), (∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = fderiv ℝ (β : DifferentialForm (Euclid P) n) y v) → R.action (γ : DifferentialForm (Euclid P) n) = 0) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, R.action (fun y => (ω : DifferentialForm (Euclid P) n) (v + y)) = R.action (ω : DifferentialForm (Euclid P) n)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.translate_derivative-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
