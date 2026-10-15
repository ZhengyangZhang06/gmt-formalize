# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1.local_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retract-cbf66c02ea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1`
- Child key: `local_inverse`
- Declaration: `Submission.dtc_bc_lr_local_inverse`
- Exact Lean type: `∀ (d : ℕ) (h : Euclid d → Euclid d) (V : Set (Euclid d)) (v₀ : Euclid d), IsOpen V → v₀ ∈ V → ContDiffOn ℝ 1 h V → fderiv ℝ h v₀ = ContinuousLinearMap.id ℝ (Euclid d) → ∃ (V₀ O : Set (Euclid d)) (k : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ V₀ ⊆ V ∧ v₀ ∈ V₀ ∧ MapsTo h V₀ O ∧ MapsTo k O V₀ ∧ (∀ v ∈ V₀, k (h v) = v) ∧ (∀ u ∈ O, h (k u) = u) ∧ ContDiffOn ℝ 1 k O ∧ fderiv ℝ k (h v₀) = ContinuousLinearMap.id ℝ (Euclid d)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
