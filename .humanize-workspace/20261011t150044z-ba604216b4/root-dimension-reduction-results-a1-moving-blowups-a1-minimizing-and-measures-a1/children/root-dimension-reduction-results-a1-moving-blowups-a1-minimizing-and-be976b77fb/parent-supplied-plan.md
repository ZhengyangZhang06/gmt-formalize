# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.minimizing_and_measures-a1.mass_lsc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-minimizing-and-be976b77fb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.minimizing_and_measures-a1`
- Child key: `mass_lsc`
- Declaration: `Submission.dimred_mbl_mm_massOn_le_liminf`
- Exact Lean type: `∀ (P n : ℕ) (Us : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ Us j) → ConvergesWeakly Ss C → ∀ φ : ℕ → ℕ, StrictMono φ → ∀ O : Set (Euclid P), C.massOn O ≤ liminf (fun i => (Ss (φ i)).massOn O) atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
