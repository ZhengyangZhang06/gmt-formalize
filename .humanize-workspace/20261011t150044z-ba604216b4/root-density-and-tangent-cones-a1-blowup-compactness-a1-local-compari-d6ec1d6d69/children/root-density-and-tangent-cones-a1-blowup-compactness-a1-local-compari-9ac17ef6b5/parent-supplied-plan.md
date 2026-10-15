# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1.pullback_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9ac17ef6b5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1`
- Child key: `pullback_cutoff`
- Declaration: `Submission.dtc_bc_lc_pf_ext_pullback_cutoff`
- Exact Lean type: `∀ (P Q n : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid Q) (ω : DifferentialForm (Euclid Q) n), IsOpen O → ContDiffOn ℝ 1 f O → IsCompact K → K ⊆ O → Continuous ω → ∃ h : Euclid P → Covector (Euclid P) n, Continuous h ∧ HasCompactSupport h ∧ ∀ x ∈ K, h x = (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
