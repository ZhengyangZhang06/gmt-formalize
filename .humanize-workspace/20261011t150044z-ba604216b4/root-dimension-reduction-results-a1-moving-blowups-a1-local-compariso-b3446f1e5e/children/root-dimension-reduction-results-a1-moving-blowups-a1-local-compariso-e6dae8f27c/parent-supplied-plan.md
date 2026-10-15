# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1.mixed_mass_triangle-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-e6dae8f27c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1`
- Child key: `mixed_mass_triangle`
- Declaration: `Submission.dimred_mbl_lc_ic_rb_massOn_le_add_incl`
- Exact Lean type: `∀ (P n : ℕ) (U V₁ V₂ G : Set (Euclid P)) (h₁ : U ⊆ V₁) (h₂ : U ⊆ V₂) (Z : GeometricCurrentOn U n) (X : GeometricCurrentOn V₁ n) (Y : GeometricCurrentOn V₂ n) (c : ℝ), (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ G → Z ω = X (testFormOnInclusion h₁ n ω) + c * Y (testFormOnInclusion h₂ n ω)) → Z.massOn G ≤ X.massOn G + ENNReal.ofReal |c| * Y.massOn G`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
