# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.piece_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-eq-theta-hausdorff-a1-piece-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1`
- Child key: `piece_identity`
- Declaration: `Submission.frt_weq_piece_restrict_eq_density`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsOpen W → μ W ≠ ∞ → A ⊆ W → μHE[n] A ≠ ∞ → NullMeasurableSet A μHE[n] → (∀ x ∈ A, 0 < θ x ∧ HasDensity n μ x (ENNReal.ofReal (θ x))) → (∀ Z ⊆ A, μHE[n] Z = 0 → μ Z = 0) → (∀ Z ⊆ A, μ Z = 0 → μHE[n] Z = 0) → (∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)).restrict A, HasDensity n ((μHE[n] : Measure (Euclidean N)).restrict A) x 1) → ∀ B : Set (Euclidean N), MeasurableSet B → μ (B ∩ A) = ∫⁻ x in B ∩ A, ENNReal.ofReal (θ x) ∂μHE[n]`

## Sibling prerequisites

- `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.lebesgue_density_subset-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
