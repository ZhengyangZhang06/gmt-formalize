# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1.limit_triple-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-limit-triple-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_completeness-a1`
- Child key: `limit_triple`
- Declaration: `Submission.imc_isRectifiableTriple_of_eventually_mem`
- Exact Lean type: `∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k) (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), (∀ j, IsRectifiableTriple (univ : Set (Eucl N)) k (M j) (θ j) (ξ j)) → (∀ j, ∀ x ∈ M j, 1 ≤ θ j x) → NullMeasurableSet M₀ (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M₀, 1 ≤ θ₀ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₀ (M₀ ∩ K) (μHE[k] : Measure (Eucl N))) → (∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict M₀), (∀ᶠ j in atTop, x ∈ M j) ∧ Tendsto (fun j => ξ j x) atTop (𝓝 (ξ₀ x))) → IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀`

## Sibling prerequisites

- `root.deformation-a1.im_completeness-a1.approx_tangent_locality-a1`
- `root.deformation-a1.im_completeness-a1.weighted_tangent_equiv-a1`
- `root.flat_iff_weak-a1.im_series-a1.frame_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
