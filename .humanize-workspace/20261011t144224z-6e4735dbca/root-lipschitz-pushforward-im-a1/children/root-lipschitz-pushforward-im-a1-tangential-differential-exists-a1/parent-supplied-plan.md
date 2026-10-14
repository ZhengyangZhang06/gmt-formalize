# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1`
- Child key: `tangential_differential_exists`
- Declaration: `Submission.lpf_tangential_differential_exists`
- Exact Lean type: `∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → ∃ L : Eucl P → (Eucl P →L[ℝ] Eucl Q), (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) ∧ AEStronglyMeasurable L ((μHE[n] : Measure (Eucl P)).restrict M) ∧ ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ M ∩ K, ‖L x‖ ≤ C`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.countably_rectifiable_c1_cover-a1`
- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
