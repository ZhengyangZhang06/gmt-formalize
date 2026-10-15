# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.eventually_near-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-measure-cl-1855270541/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1`
- Child key: `eventually_near`
- Declaration: `Submission.dimred_tr_mcr_eventually_near`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)) (Ss : ℕ → Set (Euclid P)), (∀ (sub : ℕ → ℕ) (z : ℕ → Euclid P) (x : Euclid P), StrictMono sub → (∀ k, z k ∈ ball (0 : Euclid P) 1 ∩ Ss (sub k)) → Tendsto z atTop (𝓝 x) → x ∈ S) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ Ss k ⊆ {x | ∃ z ∈ S, dist x z < ε}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
