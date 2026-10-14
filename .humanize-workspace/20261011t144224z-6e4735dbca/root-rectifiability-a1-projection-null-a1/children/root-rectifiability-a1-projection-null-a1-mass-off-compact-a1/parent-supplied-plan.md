# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.mass_off_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `mass_off_compact`
- Declaration: `Submission.rpn_massOn_le_mul_measure_diff`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)), (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) → ∀ (μ : Measure (Eucl P)) (ξ : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ ξ → (∀ᵐ x ∂μ, ∑ β : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate (ξ x) β) ^ 2 = 1) → ∀ (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (K : Set (Eucl P)), IsCompact K → (∀ α : SimonMultiIndex (m + 1) P, (volume : Measure (Eucl (m + 1))) ((fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1))) '' K) = 0) → ∃ C : ℝ≥0, ∀ W, CompactlyContainedOpen W U → T.massOn W ≤ (C : ℝ≥0∞) * μ (W \ K)`

## Sibling prerequisites

- `root.rectifiability-a1.projection_null-a1.pullback_top_form_bound-a1`
- `root.rectifiability-a1.projection_null-a1.covector_rotated_expansion-a1`
- `root.rectifiability-a1.projection_null-a1.null_compact_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
