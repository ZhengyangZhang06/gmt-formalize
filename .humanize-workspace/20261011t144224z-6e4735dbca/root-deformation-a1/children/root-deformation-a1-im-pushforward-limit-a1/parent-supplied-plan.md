# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1`
- Child key: `im_pushforward_limit`
- Declaration: `Submission.deformation_im_pushforward_limit`
- Exact Lean type: `LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) k) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → (∀ x ∈ M, ∃ j : ℕ, θ x = j) → (∀ ω : TestFormOn (univ : Set (Eucl P)) k, X ω = tauAction k M θ ξ ω) → ∀ (g : Eucl P → Eucl Q) (Λ : ℝ≥0), LipschitzWith Λ g → (∀ K : Set (Eucl Q), IsCompact K → IsCompact (g ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl Q)) k, IsLipschitzPushforward X g S ∧ IsIntegerMultiplicity S ∧ ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : TestFormOn (univ : Set (Eucl Q)) k, Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) ((ω : DifferentialForm (Eucl Q) k) (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (S ω))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
