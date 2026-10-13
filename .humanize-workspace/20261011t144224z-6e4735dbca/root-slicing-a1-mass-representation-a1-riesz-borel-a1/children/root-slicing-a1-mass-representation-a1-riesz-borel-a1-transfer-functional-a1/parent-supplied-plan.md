# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.riesz_borel-a1.transfer_functional-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-riesz-borel-a1-transfer-functional-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.riesz_borel-a1`
- Child key: `transfer_functional`
- Declaration: `Submission.smr_rb_transfer_functional`
- Exact Lean type: `∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ (Fin N)) → ℝ, (∀ f g : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f → tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U → L (f + g) = L f + L g) → (∀ (c : ℝ) (f : Eucl P → EuclideanSpace ℝ (Fin N)), Continuous f → HasCompactSupport f → tsupport f ⊆ U → L (c • f) = c * L f) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ, ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → tsupport f ⊆ K → (∀ x, ‖f x‖ ≤ 1) → L f ≤ B) → ∃ L' : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ, (∀ K : Set ↥U, IsCompact K → ∃ B : ℝ, ∀ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)), (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L' g ≤ B) ∧ ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)), (∀ y : ↥U, g y = f ↑y) ∧ L f = L' g`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
