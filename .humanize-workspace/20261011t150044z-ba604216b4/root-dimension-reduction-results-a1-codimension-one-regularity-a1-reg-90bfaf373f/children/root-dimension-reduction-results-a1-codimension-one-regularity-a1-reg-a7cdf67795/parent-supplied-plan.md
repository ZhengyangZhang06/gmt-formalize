# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1`
- Child key: `bv_compactness`
- Declaration: `Submission.codim1_rdo_dg_bv_set_compactness`
- Exact Lean type: `∀ (m : ℕ) (Fs : ℕ → Set (Euclid (m + 1))), (∀ k, MeasurableSet (Fs k)) → (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ k in atTop, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → (∀ z, ‖g z‖ ≤ 1) → ∫ z in Fs k, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (ψ : ℕ → ℕ) (F₀ : Set (Euclid (m + 1))), StrictMono ψ ∧ MeasurableSet F₀ ∧ ∀ R : ℝ, Tendsto (fun j => volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R)) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
