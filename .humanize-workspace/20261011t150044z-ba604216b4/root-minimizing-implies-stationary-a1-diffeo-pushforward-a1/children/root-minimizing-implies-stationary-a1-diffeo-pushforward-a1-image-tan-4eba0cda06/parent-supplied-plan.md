# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-4eba0cda06/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child key: `image_tangent_transport`
- Declaration: `Submission.dpf_approxTangent_bilipschitz_image_ae`
- Exact Lean type: `∀ (P n : ℕ) (U M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), IsOpen U → MeasurableSet M → M ⊆ U → CountablyRectifiable n M → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (M ∩ C) ≠ ∞) → ContDiff ℝ 1 φ → (∀ x, Injective (fderiv ℝ φ x)) → LipschitzWith Λ φ → AntilipschitzWith Λ φ → φ ⁻¹' U = U → ∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (approxTangentPlane n M x) ∧ HasApproximateTangentSpaceAt n (φ '' M) (φ x) (Submodule.map (fderiv ℝ φ x : Euclid P →ₗ[ℝ] Euclid P) (approxTangentPlane n M x))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_pieces-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
