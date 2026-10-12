# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.local_to_global_im-a1.tau_unique_on_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-unique-on-open-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child key: `tau_unique_on_open`
- Declaration: `Submission.ltg_tau_unique_on_open`
- Exact Lean type: `∀ (P k : ℕ) (U O : Set (Eucl P)), IsOpen O → O ⊆ U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (ξ₁ ξ₂ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M₁ θ₁ ξ₁ → IsRectifiableTriple U k M₂ θ₂ ξ₂ → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O → tauAction k M₁ θ₁ ξ₁ ω = tauAction k M₂ θ₂ ξ₂ ω) → (μHE[k] : Measure (Eucl P)) (symmDiff M₁ M₂ ∩ O) = 0 ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ O)), θ₁ x = θ₂ x ∧ ξ₁ x = ξ₂ x`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_integrable-a1`
- `root.boundary_rectifiability-a1.local_to_global_im-a1.covector_separating-a1`
- `root.boundary_rectifiability-a1.local_to_global_im-a1.simple_unit_rigidity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
