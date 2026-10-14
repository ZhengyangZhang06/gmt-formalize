# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.globalize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-globalize-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1`
- Child key: `globalize`
- Declaration: `Submission.constancy_of_local_constancy`
- Exact Lean type: `∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → IsConnected U → ∀ T : GeometricCurrentOn U (m + 1), (∀ x₀ ∈ U, ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧ ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) ⊆ ball x₀ r → T ω = c * ∫ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), T ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
