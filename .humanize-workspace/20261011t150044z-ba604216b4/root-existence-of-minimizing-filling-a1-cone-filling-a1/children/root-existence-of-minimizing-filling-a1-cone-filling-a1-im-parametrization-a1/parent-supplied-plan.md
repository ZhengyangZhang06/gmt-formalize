# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.im_parametrization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-im-parametrization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1`
- Child key: `im_parametrization`
- Declaration: `Submission.ecf_im_lipschitz_parametrization`
- Exact Lean type: `∀ (k P : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) k), IsIntegerMultiplicity S → IsCompact S.support → S.mass ≠ ∞ ∧ ∃ (F : ℕ → Euclid k → Euclid P) (A : ℕ → Set (Euclid k)) (g : ℕ → Euclid k → ℤ), (∀ j, ∃ K : NNReal, LipschitzWith K (F j)) ∧ (∀ j, MeasurableSet (A j)) ∧ (∀ j, Measurable (g j)) ∧ (∀ j, IntegrableOn (fun u => (g j u : ℝ)) (A j)) ∧ (∀ j, ∀ u ∈ A j, DifferentiableAt ℝ (F j) u) ∧ (∀ j, F j '' A j ⊆ S.support) ∧ ∑' j, ∫⁻ u in A j, ‖(g j u : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ (F j) u (EuclideanSpace.single a 1)) (fderiv ℝ (F j) u (EuclideanSpace.single b 1))))) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => ∫ u in A j, (g j u : ℝ) * (ω : DifferentialForm (Euclid P) k) (F j u) (fun a => fderiv ℝ (F j) u (EuclideanSpace.single a 1))) (S ω)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.parametric_rep-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
