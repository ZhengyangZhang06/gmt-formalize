# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.riesz_borel-a1.pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-riesz-borel-a1-pushforward-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.riesz_borel-a1`
- Child key: `pushforward`
- Declaration: `Submission.smr_rb_pushforward_subtype`
- Exact Lean type: `∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (m : Measure ↥U) (ν₁ : ↥U → EuclideanSpace ℝ (Fin N)), (∀ K : Set ↥U, IsCompact K → m K < ∞) → Measurable ν₁ → (∀ y, ‖ν₁ y‖ ≤ 1) → (∀ᵐ y ∂m, ‖ν₁ y‖ = 1) → ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable ν ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ x, ‖ν x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f → tsupport f ⊆ U → Integrable (fun x => inner ℝ (f x) (ν x)) μ ∧ ∫ x, inner ℝ (f x) (ν x) ∂μ = ∫ y, inner ℝ (f ↑y) (ν₁ y) ∂m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
