# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.close_subset-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ad3ed3a238/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child key: `close_subset`
- Declaration: `Submission.codim1_rdo_dg_bvc_infinite_close_subset`
- Exact Lean type: `∀ (n : ℕ) (Fs : ℕ → Set (Euclid n)), (∀ R : ℝ, 0 < R → ∀ θ : ℝ, 0 < θ → ∃ S : Finset ℕ, ∀ k, ∃ i ∈ S, volume (symmDiff (Fs k) (Fs i) ∩ ball (0 : Euclid n) R) < ENNReal.ofReal θ) → ∀ (r : ℕ) (I : Set ℕ), I.Infinite → ∃ J ⊆ I, J.Infinite ∧ ∀ j ∈ J, ∀ l ∈ J, volume (symmDiff (Fs j) (Fs l) ∩ ball (0 : Euclid n) ((r : ℝ) + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
