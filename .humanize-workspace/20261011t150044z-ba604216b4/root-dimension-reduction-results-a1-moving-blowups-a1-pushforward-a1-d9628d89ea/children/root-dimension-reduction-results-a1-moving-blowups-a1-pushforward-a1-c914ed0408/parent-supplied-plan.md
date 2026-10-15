# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.bilip_partition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-c914ed0408/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1`
- Child key: `bilip_partition`
- Declaration: `Submission.dimred_mbl_pfi_bilipschitz_partition`
- Exact Lean type: `∀ (P n : ℕ) (H : Euclid n → Euclid P) (B : Set (Euclid n)), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → ∃ (C : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ l, MeasurableSet (C l)) ∧ Pairwise (fun k l => Disjoint (C k) (C l)) ∧ (⋃ l, C l) = B ∧ (∀ l, 0 < m l) ∧ ∀ l, ∀ a ∈ C l, ∀ a' ∈ C l, m l * ‖a - a'‖ ≤ ‖H a - H a'‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
