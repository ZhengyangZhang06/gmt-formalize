# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_density_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1-t-2c180ab89c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1`
- Child key: `top_density_unique`
- Declaration: `Submission.ind_top_form_density_ae_unique`
- Exact Lean type: `∀ (m : ℕ) (U : Set (Eucl (m + 1))) (u v : Eucl (m + 1) → ℝ), IsOpen U → (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) → (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn v K volume) → (∀ ω : TestFormOn U (m + 1), ∫ x in U, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume = ∫ x in U, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → u x = v x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
