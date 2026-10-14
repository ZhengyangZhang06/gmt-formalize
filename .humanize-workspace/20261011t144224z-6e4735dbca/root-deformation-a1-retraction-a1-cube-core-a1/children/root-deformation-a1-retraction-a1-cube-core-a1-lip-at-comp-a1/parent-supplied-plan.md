# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.retraction-a1.cube_core-a1.lip_at_comp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1-cube-core-a1-lip-at-comp-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.retraction-a1.cube_core-a1`
- Child key: `lip_at_comp`
- Declaration: `Submission.dr_cc_lip_at_comp`
- Exact Lean type: `∀ (X Y Z : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z] (f : X → Y) (g : Y → Z) (A : Set X) (B : Set Y) (x : X) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ → MapsTo f A B → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (f x') (f x) ≤ (K₁ + ε) * dist x' x) → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' (f x) < δ → dist (g y') (g (f x)) ≤ (K₂ + ε) * dist y' (f x)) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (g (f x')) (g (f x)) ≤ (K₁ * K₂ + ε) * dist x' x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
