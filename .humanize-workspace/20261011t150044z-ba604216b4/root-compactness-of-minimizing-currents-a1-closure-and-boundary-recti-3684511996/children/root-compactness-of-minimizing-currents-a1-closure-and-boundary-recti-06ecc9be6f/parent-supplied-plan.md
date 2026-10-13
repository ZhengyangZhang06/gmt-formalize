# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.steiner_reflect-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-06ecc9be6f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1`
- Child key: `steiner_reflect`
- Declaration: `Submission.cbr_ci_iso_steiner_reflection`
- Exact Lean type: `∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), (∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}) ∧ ∀ i : Fin d, i ≠ j → (∀ x ∈ A, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ A) → ∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
