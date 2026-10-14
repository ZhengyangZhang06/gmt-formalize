# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.cyl_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-36d21f0b90/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1`
- Child key: `cyl_fubini`
- Declaration: `Submission.cmcdt_lpi_cyl_fubini`
- Exact Lean type: `∀ (n : ℕ) (A : Set (Euclid n)), MeasurableSet A → MeasurableSet {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} ∧ (∀ f : Euclid (n + 1) → ℝ≥0∞, Measurable f → ∫⁻ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫⁻ u in A, ∫⁻ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))) ∧ ∀ f : Euclid (n + 1) → ℝ, IntegrableOn f {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → ∫ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫ u in A, ∫ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
