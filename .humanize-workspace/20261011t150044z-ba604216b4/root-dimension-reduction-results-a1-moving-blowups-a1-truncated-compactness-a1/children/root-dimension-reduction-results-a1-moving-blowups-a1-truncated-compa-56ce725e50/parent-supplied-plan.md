# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.weak_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compa-56ce725e50/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Child key: `weak_compactness`
- Declaration: `Submission.dimred_mbl_tc_weak_compactness`
- Exact Lean type: `∀ (P n : ℕ) (T : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ R : ℝ, ⨆ j, (T j).massOn (ball (0 : Euclid P) R) < ∞) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), StrictMono φ ∧ WeaklyConvergesOn (fun i => T (φ i)) C`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`
- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.covector_euclidean_equiv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
