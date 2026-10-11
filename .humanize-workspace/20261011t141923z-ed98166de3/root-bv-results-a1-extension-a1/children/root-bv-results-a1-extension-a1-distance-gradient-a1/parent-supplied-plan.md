# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.extension-a1.distance_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-extension-a1-distance-gradient-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.extension-a1`
- Child key: `distance_gradient`
- Declaration: `Submission.bv_ext_norm_fderiv_infDist_eq_one`
- Exact Lean type: `∀ (n : ℕ) (S : Set (Rn n)) (x : Rn n), IsClosed S → S.Nonempty → x ∉ S → DifferentiableAt ℝ (fun y ↦ infDist y S) x → ‖fderiv ℝ (fun y ↦ infDist y S) x‖ = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
