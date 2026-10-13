# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.good_level-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-7494d4e9b1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child key: `good_level`
- Declaration: `Submission.dtc_bc_lc_good_level`
- Exact Lean type: `∀ (P : ℕ) (g : ℕ → ℝ → ℝ≥0∞) (μ : ℕ → Measure (Euclid P)) (h : Euclid P → ℝ) (good : ℕ → ℝ → Prop) (a b : ℝ), a < b → Measurable h → (∀ i, AEMeasurable (g i) (volume.restrict (Ioo a b))) → (∑' i, ∫⁻ t in Ioo a b, g i t) ≠ ∞ → (∀ i, μ i {x | a < h x ∧ h x < b} ≠ ∞) → (∀ i, ∀ᵐ t, good i t) → ∃ t ∈ Ioo a b, (∀ i, good i t) ∧ (∑' i, g i t) ≠ ∞ ∧ ∀ i, μ i {x | h x = t} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
