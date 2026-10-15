# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.fibre_signed-a1.signed_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b9cc4da205/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.fibre_signed-a1`
- Child key: `signed_transfer`
- Declaration: `Submission.idtp_cse_fd_fs_pushforward_signed_transfer`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (φ : X → ℝ × ℝ) (g : X → ℝ) (H : ℝ × ℝ → ℝ≥0∞), ν univ ≠ ∞ → Measurable φ → AEStronglyMeasurable g ν → (∀ᵐ x ∂ν, 0 ≤ g x ∧ g x ≤ 1) → AEMeasurable H volume → (∀ b : ℝ × ℝ → ℝ≥0∞, Measurable b → ∫⁻ p : ℝ × ℝ, b p * H p = ∫⁻ x, b (φ x) * ENNReal.ofReal (g x) ∂ν) → (∀ᵐ p : ℝ × ℝ, H p ≠ ∞) ∧ Integrable (fun p : ℝ × ℝ => (H p).toReal) ∧ (∀ b : ℝ × ℝ → ℝ, Measurable b → (∃ M : ℝ, ∀ p, |b p| ≤ M) → ∫ p : ℝ × ℝ, b p * (H p).toReal = ∫ x, b (φ x) * g x ∂ν) ∧ ∀ S : Set (ℝ × ℝ), MeasurableSet S → ∫⁻ p in S, H p = ∫⁻ x in φ ⁻¹' S, ENNReal.ofReal (g x) ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
