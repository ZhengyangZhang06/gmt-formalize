# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.density_dominated-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1-density-dominated-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1`
- Child key: `density_dominated`
- Declaration: `Submission.lpf_pic_density_dominated`
- Exact Lean type: `∀ (P Q n : ℕ) (U Z M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (K : Set (Eucl Q)), IsRectifiableTriple U n M θ ξ → Z ⊆ U → (μHE[n] : Measure (Eucl P)) (M \ Z) = 0 → IsCompact (f ⁻¹' K ∩ Z) → (∃ C : ℝ, ∀ x ∈ M ∩ (f ⁻¹' K ∩ Z), ‖L x‖ ≤ C) → ∃ h : Eucl P → ℝ, Integrable h ((μHE[n] : Measure (Eucl P)).restrict M) ∧ ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), f x ∈ K → ‖θ x • nVectorPushforward n (L x) (ξ x)‖ ≤ h x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
