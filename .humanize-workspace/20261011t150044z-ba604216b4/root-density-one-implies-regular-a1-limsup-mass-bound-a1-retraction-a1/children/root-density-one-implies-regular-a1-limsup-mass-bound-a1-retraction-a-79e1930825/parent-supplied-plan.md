# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.uniform_injectivity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-79e1930825/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1`
- Child key: `uniform_injectivity`
- Declaration: `Submission.dor_lmb_ret_uniform_injectivity`
- Exact Lean type: `∀ (P d : ℕ) (K : Set (Euclid d)) (L : Euclid d → (Euclid d →L[ℝ] Euclid P)), IsCompact K → ContinuousOn L K → (∀ v ∈ K, Injective (L v)) → ∃ b : ℝ, 0 ≤ b ∧ ∀ v ∈ K, ∀ w : Euclid d, ‖w‖ ≤ b * ‖L v w‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
