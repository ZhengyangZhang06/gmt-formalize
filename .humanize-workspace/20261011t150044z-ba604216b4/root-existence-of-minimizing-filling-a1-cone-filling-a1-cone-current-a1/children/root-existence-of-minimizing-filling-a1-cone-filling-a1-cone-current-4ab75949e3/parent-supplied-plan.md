# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1.homotopy_toolkit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-current-4ab75949e3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1`
- Child key: `homotopy_toolkit`
- Declaration: `Submission.ecf_cc_radial_homotopy_toolkit`
- Exact Lean type: `∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)), Continuous β → (∀ (x : Euclid P) (v : Fin m → Euclid P), (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) v = ∫ t in (0 : ℝ)..1, t ^ m * β (t • x) (Fin.cons x v)) ∧ (∀ (c : ℝ) (x : Euclid P), (∀ y : Euclid P, covectorEuclideanNorm (β y) ≤ c) → covectorEuclideanNorm (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) ≤ ‖x‖ * c) ∧ (∀ x : Euclid P, (∀ t ∈ Icc (0 : ℝ) 1, β (t • x) = 0) → (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) = 0) ∧ (∀ β' : DifferentialForm (Euclid P) (m + 1), Continuous β' → ∀ x : Euclid P, (∫ t in (0 : ℝ)..1, t ^ m • ((β + β') (t • x)).curryLeft x) = (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) + ∫ t in (0 : ℝ)..1, t ^ m • (β' (t • x)).curryLeft x) ∧ ∀ (c : ℝ) (x : Euclid P), (∫ t in (0 : ℝ)..1, t ^ m • ((c • β) (t • x)).curryLeft x) = c • ∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1.covector_bound-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1.curry_le-a1`
- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.norm_props-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
