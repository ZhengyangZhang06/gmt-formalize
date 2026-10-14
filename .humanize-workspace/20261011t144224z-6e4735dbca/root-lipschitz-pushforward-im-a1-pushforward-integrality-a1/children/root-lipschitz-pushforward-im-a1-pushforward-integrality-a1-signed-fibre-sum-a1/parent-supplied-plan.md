# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.signed_fibre_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-signed-fibre-sum-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child key: `signed_fibre_sum`
- Declaration: `Submission.lpf_pi_signed_fibre_sum`
- Exact Lean type: `∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (f : X → Y) (A : Set X) (J : X → ℝ≥0∞), AEMeasurable J (μ.restrict A) → (∀ h : X → ℝ≥0∞, AEMeasurable h (μ.restrict A) → AEMeasurable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, h x) ν ∧ ∫⁻ x in A, h x * J x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, h x ∂ν) → ∀ g : X → ℝ, AEStronglyMeasurable g (μ.restrict A) → ∫⁻ x in A, ‖g x‖ₑ * J x ∂μ < ∞ → (∀ᵐ y ∂ν, Summable (fun x : {x : X // x ∈ A ∧ f x = y} => g x)) ∧ Integrable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, g x) ν ∧ ∫ x in A, g x * (J x).toReal ∂μ = ∫ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, g x ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
