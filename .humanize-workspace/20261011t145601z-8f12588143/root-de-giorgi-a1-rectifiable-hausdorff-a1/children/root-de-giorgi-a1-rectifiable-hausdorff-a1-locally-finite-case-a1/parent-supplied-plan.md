# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.locally_finite_case-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-locally-finite-case-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child key: `locally_finite_case`
- Declaration: `Submission.deGiorgiRH_locallyFinite_case`
- Exact Lean type: `(∀ (n ℓ : ℕ) (μ : Measure (Rn (n + ℓ))), (∀ K : Set (Rn (n + ℓ)), IsCompact K → μ K < ∞) → (∀ᵐ x ∂μ, ∃ (P : Submodule ℝ (Rn (n + ℓ))) (θ : ℝ), 0 < θ ∧ HasApproxTangentPlaneWithMultiplicity n μ x P θ) → ∃ R : Set (Rn (n + ℓ)), MeasurableSet R ∧ CountablyRectifiable n R ∧ μ Rᶜ = 0) → ApproximateTangentCharacterization → ∀ (n ℓ : ℕ) (S : Set (Rn (n + ℓ))) (μ : Measure (Rn (n + ℓ))), (∀ K : Set (Rn (n + ℓ)), IsCompact K → μ K < ∞) → MeasurableSet S → μ Sᶜ = 0 → (∀ x ∈ S, ∃ P : Submodule ℝ (Rn (n + ℓ)), HasApproxTangentPlaneWithMultiplicity n μ x P 1) → CountablyRectifiable n S ∧ μ = (μHE[n] : Measure (Rn (n + ℓ))).restrict S`

## Sibling prerequisites

- `root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_density-a1`
- `root.de_giorgi-a1.rectifiable_hausdorff-a1.hausdorff_density-a1`
- `root.de_giorgi-a1.rectifiable_hausdorff-a1.hausdorff_le_measure-a1`
- `root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_le_hausdorff-a1`
- `root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_eq_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
