# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.retraction-a1.cube_core-a1.lip_at_union-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1-cube-core-a1-lip-at-union-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.retraction-a1.cube_core-a1`
- Child key: `lip_at_union`
- Declaration: `Submission.dr_cc_lip_at_union`
- Exact Lean type: `∀ (X Y : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] (ι : Type) [Finite ι] (G : ι → Set X) (B : Set X) (g : X → Y) (y : X) (K : ℝ), (∀ k, IsClosed (G k)) → B ⊆ ⋃ k, G k → (∀ k, y ∈ G k → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ G k ∩ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
