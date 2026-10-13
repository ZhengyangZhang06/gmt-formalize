# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1.signed_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-ac83ea4a00/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1`
- Child key: `signed_density`
- Declaration: `Submission.dgid_imrep_signed_density_representation`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (W S : Set (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), MeasurableSet S → μHE[n] ((R.carrier ∩ W) \ S) = 0 → AEStronglyMeasurable β (μHE[n].restrict S) → (∀ x ∈ S, ξ x (β x) = 1) → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ S)), R.orient x = ξ x ∨ R.orient x = -ξ x) → ∃ g : Euclid P → ℝ, AEStronglyMeasurable g (μHE[n].restrict S) ∧ (∀ᵐ x ∂(μHE[n].restrict S), (∃ m : ℤ, g x = m) ∧ ‖g x‖ₑ ≤ R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x) ∧ ∀ ω : DifferentialForm (Euclid P) n, tsupport ω ⊆ W → R.action ω = ∫ x in S, g x * ξ x (ω x) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
