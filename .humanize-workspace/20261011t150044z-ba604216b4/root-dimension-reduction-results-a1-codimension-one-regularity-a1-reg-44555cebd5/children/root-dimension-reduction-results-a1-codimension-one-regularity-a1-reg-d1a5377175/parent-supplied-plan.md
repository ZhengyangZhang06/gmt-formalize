# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.normal_orientation-a1.det_normal_decomp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-d1a5377175/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.normal_orientation-a1`
- Child key: `det_normal_decomp`
- Declaration: `Submission.codim1_lur_no_det_cons_normal_decomp`
- Exact Lean type: `∀ (n : ℕ) (ν w : Euclid (n + 1)) (σ : Fin n → Euclid (n + 1)), ‖ν‖ = 1 → Submodule.span ℝ (Set.range σ) = (Submodule.span ℝ {ν})ᗮ → Matrix.det (Matrix.of fun r c : Fin (n + 1) => (Fin.cons w σ : Fin (n + 1) → Euclid (n + 1)) c r) = inner ℝ w ν * Matrix.det (Matrix.of fun r c : Fin (n + 1) => (Fin.cons ν σ : Fin (n + 1) → Euclid (n + 1)) c r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
