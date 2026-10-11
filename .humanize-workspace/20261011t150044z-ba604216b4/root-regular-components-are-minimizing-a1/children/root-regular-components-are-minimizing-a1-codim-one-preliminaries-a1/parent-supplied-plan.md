# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-codim-one-preliminaries-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1`
- Child key: `codim_one_preliminaries`
- Declaration: `Submission.regcomp_codim_one_preliminaries`
- Exact Lean type: `∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1)) (T : GeometricCurrentOn U n), IsOpen U → InClassO n U N ξN → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → IsMinimizingIn T (N ∩ U) → 1 ≤ k ∧ T.support ⊆ N ∧ BoundaryVanishes T ∧ (n = 0 → regularSet T = ∅)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
