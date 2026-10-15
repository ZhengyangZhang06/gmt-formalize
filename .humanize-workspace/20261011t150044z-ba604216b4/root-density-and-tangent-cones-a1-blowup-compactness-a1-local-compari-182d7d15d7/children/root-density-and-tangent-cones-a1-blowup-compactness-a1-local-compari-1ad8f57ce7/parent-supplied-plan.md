# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.glue_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-1ad8f57ce7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Child key: `glue_pieces`
- Declaration: `Submission.dtc_bc_lc_pfi_isIntegerMultiplicity_of_pieces`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (N : ℕ → Set (Euclid P)) (g : ℕ → Euclid P → ℤ) (η : ℕ → Euclid P → MultiVector P n) (Q : GeometricCurrentOn U n), IsOpen U → (∀ j, MeasurableSet (N j)) → (∀ j, N j ⊆ U) → (∀ j, CountablyRectifiable n (N j)) → (∀ j, Measurable (g j)) → (∀ j, ∀ y ∈ N j, g j y ≠ 0) → (∀ j, StronglyMeasurable (η j)) → (∀ j, ∀ᵐ y ∂(μHE[n].restrict (N j)), ∃ T : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (N j) y T ∧ IsUnitOrientationOf (η j y) T) → ∑' j, ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ → (∀ ω : TestFormOn U n, Q ω = ∑' j, ∫ y in N j, (g j y : ℝ) * η j y ((ω : DifferentialForm (Euclid P) n) y) ∂μHE[n]) → IsIntegerMultiplicity Q`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.orient_algebra-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1.density_imrep-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.int_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
