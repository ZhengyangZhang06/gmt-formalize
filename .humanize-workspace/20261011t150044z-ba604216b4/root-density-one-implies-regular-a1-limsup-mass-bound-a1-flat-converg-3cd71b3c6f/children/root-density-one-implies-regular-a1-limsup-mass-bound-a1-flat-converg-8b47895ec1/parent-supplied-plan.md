# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.regular_partition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-8b47895ec1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`
- Child key: `regular_partition`
- Declaration: `Submission.dor_lmb_fcd_imp_regular_partition`
- Exact Lean type: `∀ (k N' : ℕ) (H : Euclid k → Euclid N') (B : Set (Euclid k)), MeasurableSet B → ∃ (A : ℕ → Set (Euclid k)) (κ : ℕ → ℝ), (∀ l, MeasurableSet (A l)) ∧ (∀ l, A l ⊆ B) ∧ Pairwise (fun l l' => Disjoint (A l) (A l')) ∧ (∀ l, 0 < κ l) ∧ (∀ l, ∀ a ∈ A l, ∀ a' ∈ A l, κ l * ‖a - a'‖ ≤ ‖H a - H a'‖) ∧ (∀ l, ∀ a ∈ A l, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) ∧ ∀ u ∈ B, DifferentiableAt ℝ H u → Injective (fderiv ℝ H u) → ∃ l, u ∈ A l`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
