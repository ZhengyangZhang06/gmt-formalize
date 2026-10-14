# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.tangent_measures-a1.blowup_integrals-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8dcb296910/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.tangent_measures-a1`
- Child key: `blowup_integrals`
- Declaration: `Submission.idtp_fons_cc_tm_blowup_integrals`
- Exact Lean type: `(∀ (P n : ℕ) (μ : Measure (Euclid P)) (G : Set (Euclid P)) (p : Euclid P) (lams : ℕ → ℝ) (f : Euclid P → ℝ), IsOpen G → p ∈ G → (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → HasCompactSupport f → ∀ᶠ j in atTop, ∫ x, f x ∂(ENNReal.ofReal ((lams j)⁻¹ ^ n) • (μ.restrict G).map (dilation p (lams j))) = ∫ x, f x ∂(ENNReal.ofReal ((lams j)⁻¹ ^ n) • μ.map (dilation p (lams j)))) ∧ ∀ (P n : ℕ) (μ : Measure (Euclid P)) (p : Euclid P) (ε : ℝ) (lams : ℕ → ℝ) (f : Euclid P → ℝ), 0 < ε → μ (ball p ε) = 0 → (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → HasCompactSupport f → ∀ᶠ j in atTop, ∫ x, f x ∂(ENNReal.ofReal ((lams j)⁻¹ ^ n) • μ.map (dilation p (lams j))) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
