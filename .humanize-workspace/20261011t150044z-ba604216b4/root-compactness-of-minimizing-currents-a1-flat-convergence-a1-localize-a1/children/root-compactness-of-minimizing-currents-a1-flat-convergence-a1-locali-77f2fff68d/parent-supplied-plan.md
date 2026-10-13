# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.dist_sublevel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-77f2fff68d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child key: `dist_sublevel`
- Declaration: `Submission.cmc_fcl_dist_sublevel_compact`
- Exact Lean type: `∀ (P : ℕ) (U C : Set (Euclid P)), IsOpen U → IsCompact C → C ⊆ U → C.Nonempty → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ r : ℝ, r ≤ δ₀ → IsCompact {x | infDist x C ≤ r} ∧ {x | infDist x C ≤ r} ⊆ U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
