# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_is_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1`
- Child key: `pushforward_is_current`
- Declaration: `Submission.lpf_pushforward_is_current`
- Exact Lean type: `∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ContinuousOn f U → (∀ K, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ T.support)) → AEStronglyMeasurable L ((μHE[n] : Measure (Eucl P)).restrict M) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ M ∩ K, ‖L x‖ ≤ C) → ∃ S : GeometricCurrentOn V n, ∀ ω : TestFormOn V n, S ω = ∫ x in M, θ x * nVectorPushforward n (L x) (ξ x) ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂(μHE[n] : Measure (Eucl P))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
