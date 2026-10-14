# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.parametrized_is_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-parametrized-is-im-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1`
- Child key: `parametrized_is_im`
- Declaration: `Submission.ecf_isIntegerMultiplicity_of_parametrization`
- Exact Lean type: `∀ (k P : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)) (F : ℕ → Euclid (k + 1) → Euclid P) (A : ℕ → Set (Euclid (k + 1))) (g : ℕ → Euclid (k + 1) → ℤ), (∀ j, ∃ K : NNReal, LipschitzWith K (F j)) → (∀ j, MeasurableSet (A j)) → (∀ j, Measurable (g j)) → (∀ j, IntegrableOn (fun u => (g j u : ℝ)) (A j)) → ∑' j, ∫⁻ u in A j, ‖(g j u : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ (F j) u (EuclideanSpace.single a 1)) (fderiv ℝ (F j) u (EuclideanSpace.single b 1))))) ≠ ∞ → (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun j => ∫ u in A j, (g j u : ℝ) * (ω : DifferentialForm (Euclid P) (k + 1)) (F j u) (fun a => fderiv ℝ (F j) u (EuclideanSpace.single a 1))) (T ω)) → IsIntegerMultiplicity T`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_pushforward-a1.piece_current-a1`
- `root.minimizing_implies_stationary-a1.covector_gram_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
