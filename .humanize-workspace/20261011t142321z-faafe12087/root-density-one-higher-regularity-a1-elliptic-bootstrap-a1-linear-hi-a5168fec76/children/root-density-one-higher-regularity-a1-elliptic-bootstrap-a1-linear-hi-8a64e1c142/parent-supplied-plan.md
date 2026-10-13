# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1.scalar_c1_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-8a64e1c142/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1`
- Child key: `scalar_c1_bounds`
- Declaration: `Submission.dohr_eb_lhr_cub_scalar_c1_bounds`
- Exact Lean type: `∀ (n : ℕ) (α : ℝ) (U K : Set (Rn n)) (f : Rn n → ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → ContDiffOn ℝ 1 f U → ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ K, ∀ y ∈ K, |f x| ≤ S ∧ |f x - f y| ≤ S * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
