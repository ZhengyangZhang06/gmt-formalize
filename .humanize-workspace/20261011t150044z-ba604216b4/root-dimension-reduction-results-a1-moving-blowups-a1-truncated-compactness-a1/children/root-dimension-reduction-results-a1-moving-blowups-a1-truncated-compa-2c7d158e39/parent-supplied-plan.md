# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.limit_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compa-2c7d158e39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Child key: `limit_transfer`
- Declaration: `Submission.dimred_mbl_tc_limit_of_agreement`
- Exact Lean type: `∀ (P m : ℕ) (Us : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : ℕ → ℝ), Tendsto ρ atTop atTop → WeaklyConvergesOn Ŝ C → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 (ρ j) → Ŝ j ω = currentEval (Ss j) (ω : DifferentialForm (Euclid P) (m + 1))) → (∀ (j : ℕ) (β : TestFormOn (univ : Set (Euclid P)) m), tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 (ρ j) → (Ŝ j).boundary β = 0) → C.boundary = 0 ∧ ConvergesWeakly Ss C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
