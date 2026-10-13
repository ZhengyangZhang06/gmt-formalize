# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.blowup_eval-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-cb96411644/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1`
- Child key: `blowup_eval`
- Declaration: `Submission.dtc_bc_cz_blowUp_eval`
- Exact Lean type: `∀ (m : ℕ) (U : Set (Euclid (m + 1))) (T : GeometricCurrentOn U (m + 1)) (x : Euclid (m + 1)) (ρ c lam : ℝ) (hlam : 0 < lam), ball x ρ ⊆ U → ((∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) ⊆ ball x ρ → T ω = c * ∫ y, (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) y ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ)) → ∀ ω : TestFormOn (univ : Set (Euclid (m + 1))) (m + 1), tsupport (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) ⊆ ball 0 (ρ / lam) → currentEval (blowUp T x lam hlam.ne') (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) = c * ∫ z, (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) z ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ)) ∧ ((∀ β : TestFormOn U m, tsupport (β : DifferentialForm (Euclid (m + 1)) m) ⊆ ball x ρ → T.boundary β = 0) → ∀ β : TestFormOn (dilation x lam '' U) m, tsupport (β : DifferentialForm (Euclid (m + 1)) m) ⊆ ball 0 (ρ / lam) → (blowUp T x lam hlam.ne').boundary β = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
