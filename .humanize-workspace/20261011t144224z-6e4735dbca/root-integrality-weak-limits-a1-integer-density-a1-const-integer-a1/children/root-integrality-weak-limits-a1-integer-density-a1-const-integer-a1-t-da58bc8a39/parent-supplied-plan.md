# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_integer_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1-t-da58bc8a39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1`
- Child key: `top_integer_density`
- Declaration: `Submission.ind_top_dim_integer_density`
- Exact Lean type: `∀ (m : ℕ) (U : Set (Eucl (m + 1))) (X : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity X → ∃ u : Eucl (m + 1) → ℝ, (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∃ k : ℤ, u x = k) ∧ (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) ∧ ∀ ω : TestFormOn U (m + 1), X ω = ∫ x in U, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.frame_sign_top-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
