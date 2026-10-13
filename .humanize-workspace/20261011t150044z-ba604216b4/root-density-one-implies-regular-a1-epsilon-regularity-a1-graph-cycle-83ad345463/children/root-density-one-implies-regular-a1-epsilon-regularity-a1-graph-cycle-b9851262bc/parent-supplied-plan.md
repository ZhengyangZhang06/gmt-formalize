# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1.dominated_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b9851262bc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1`
- Child key: `dominated_pullback`
- Declaration: `Submission.dgid_dominated_pullback_integer_locallyIntegrable`
- Exact Lean type: `∀ (n P : ℕ) (Φ : Euclid n → Euclid P) (D : Set (Euclid n)) (g : Euclid P → ℝ) (F : Euclid P → ℝ≥0∞), IsOpen D → ContinuousOn Φ D → (∀ (A : Set (Euclid n)) (f : Euclid P → ℝ≥0∞), MeasurableSet A → A ⊆ D → Measurable f → ∫⁻ v in A, f (Φ v) ≤ ∫⁻ x in Φ '' A, f x ∂μHE[n]) → Measurable F → (∀ K : Set (Euclid n), IsCompact K → K ⊆ D → ∫⁻ x in Φ '' K, F x ∂μHE[n] ≠ ∞) → AEStronglyMeasurable g (μHE[n].restrict (Φ '' D)) → (∀ᵐ x ∂(μHE[n].restrict (Φ '' D)), (∃ m : ℤ, g x = m) ∧ ‖g x‖ₑ ≤ F x) → LocallyIntegrableOn (fun v => g (Φ v)) D volume ∧ ∀ᵐ v ∂(volume.restrict D), ∃ m : ℤ, g (Φ v) = m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
