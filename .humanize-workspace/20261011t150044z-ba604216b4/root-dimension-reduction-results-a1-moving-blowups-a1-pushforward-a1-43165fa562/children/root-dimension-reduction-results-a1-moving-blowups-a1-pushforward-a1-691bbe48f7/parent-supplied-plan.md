# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.orient_comp-a1.hs_comp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-691bbe48f7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.orient_comp-a1`
- Child key: `hs_comp`
- Declaration: `Submission.dimred_mbl_pf_oc_multilinear_hs_comp_le`
- Exact Lean type: `∀ (N N' n : ℕ) (A : Euclid N →L[ℝ] Euclid N') (γ : MultilinearMap ℝ (fun _ : Fin n => Euclid N') ℝ), ∑ j : Fin n → Fin N, (γ (fun k => A (EuclideanSpace.basisFun (Fin N) ℝ (j k)))) ^ 2 ≤ (‖A‖ ^ 2) ^ n * ∑ j : Fin n → Fin N', (γ (fun k => EuclideanSpace.basisFun (Fin N') ℝ (j k))) ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
