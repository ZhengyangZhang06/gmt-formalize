# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1.integral_image_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-18e0d65ecd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1`
- Child key: `integral_image_transfer`
- Declaration: `Submission.codim1_pfr_setIntegral_image_transfer`
- Exact Lean type: `∀ (m d P : ℕ) (B B' : Set (Euclid d)) (G : Euclid d → Euclid P) (J h : Euclid d → ℝ) (g : Euclid P → ℝ), MeasurableSet B → MeasurableSet B' → B' ⊆ B → ContinuousOn G B → InjOn G B → (∀ f : Euclid P → ℝ, ∫ w in G '' B, f w ∂μHE[m] = ∫ v in B, J v * f (G v) ∂μHE[m]) → (∀ᵐ v ∂(μHE[m].restrict B), h v = B'.indicator (fun y => J y * g (G y)) v) → ∫ v in B, h v ∂μHE[m] = ∫ w in G '' B', g w ∂μHE[m]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
