# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.imrep_of_subset-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4d6ef43151/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child key: `imrep_of_subset`
- Declaration: `Submission.dtc_bc_lc_sl_sf_imrep_of_subset`
- Exact Lean type: `∀ (P n : ℕ) (A S : Set (Euclid P)) (θ : Euclid P → ℕ) (ζ : Euclid P → MultiVector P n), MeasurableSet A → MeasurableSet S → A ⊆ S → CountablyRectifiable n S → Measurable θ → (∀ x ∈ S, 0 < θ x) → (∀ K : Set (Euclid P), IsCompact K → ∫⁻ x in S ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞) → AEStronglyMeasurable ζ (μHE[n].restrict A) → (∀ᵐ x ∂(μHE[n].restrict A), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n S x Q ∧ IsUnitOrientationOf (ζ x) Q) → ∃ R : IMRep (univ : Set (Euclid P)) n, R.carrier = A ∧ R.mult = θ ∧ R.orient = ζ`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
