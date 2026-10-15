# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.minimizing_and_measures-a1.limsup_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-minimizing-and-694c4d7029/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.minimizing_and_measures-a1`
- Child key: `limsup_criterion`
- Declaration: `Submission.dimred_mbl_mm_limsup_le_of_subseq`
- Exact Lean type: `∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ (K : Set (Euclid P)) (ε : ℝ), IsCompact K → 0 < ε → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ W : Set (Euclid P), K ⊆ W ∧ W ⊆ thickening ε K ∧ ∃ φ' : ℕ → ℕ, StrictMono φ' ∧ limsup (fun i => μs (ψ (φ' i)) W) atTop ≤ μ W) → ∀ K : Set (Euclid P), IsCompact K → limsup (fun j => μs j K) atTop ≤ μ K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
