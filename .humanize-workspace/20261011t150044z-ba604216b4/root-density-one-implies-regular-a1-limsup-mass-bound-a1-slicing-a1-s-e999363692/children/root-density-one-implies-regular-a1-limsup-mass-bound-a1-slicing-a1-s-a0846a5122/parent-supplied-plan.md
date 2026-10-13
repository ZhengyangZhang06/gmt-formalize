# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.image_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-a0846a5122/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `image_tangent`
- Declaration: `Submission.dor_lmbsf_c1_image_approxTangent`
- Exact Lean type: `∀ (k P : ℕ) (V C : Set (Euclid k)) (χ : Euclid k → Euclid P) (y : Euclid k), IsOpen V → ContDiffOn ℝ 1 χ V → IsCompact C → C ⊆ V → InjOn χ C → y ∈ interior C → Injective (fderiv ℝ χ y) → HasApproximateTangentSpaceAt k (χ '' C) (χ y) (LinearMap.range (fderiv ℝ χ y : Euclid k →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
