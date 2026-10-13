# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1-polar-form-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1`
- Child key: `polar_form`
- Declaration: `Submission.imc_mlb_exists_form_lintegral_coordNorm_le`
- Exact Lean type: `∀ (N k : ℕ) (μ : Measure (Eucl N)) (κ : Eucl N → NVector (Eucl N) k) (R : ℝ), (∀ γ : SimonMultiIndex k N, IntegrableOn (fun x => euclideanNVectorCoordinate (κ x) γ) (ball (0 : Eucl N) R) μ) → ∀ ε : ℝ, 0 < ε → ∃ ω : Eucl N → Covector (Eucl N) k, Continuous ω ∧ tsupport ω ⊆ ball (0 : Eucl N) R ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ Integrable (fun x => κ x (ω x)) μ ∧ ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ ENNReal.ofReal (∫ x, κ x (ω x) ∂μ + ε)`

## Sibling prerequisites

- `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_field-a1`
- `root.slicing-a1.mass_representation-a1.covector_isometry-a1.coord_sum_wedge-a1`
- `root.slicing-a1.mass_representation-a1.covector_isometry-a1.norm_coord-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
