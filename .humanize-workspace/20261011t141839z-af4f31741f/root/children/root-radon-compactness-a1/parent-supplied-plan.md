# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radon_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-radon-compactness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `radon_compactness`
- Declaration: `Submission.varifold_radon_compactness`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (μ : ℕ → Measure (Euclidean N × Grassmannian N n)), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ j in atTop, μ j (K ×ˢ (univ : Set (Grassmannian N n))) ≤ C) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : Varifold N n U, ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ U ×ˢ (univ : Set (Grassmannian N n)) → Tendsto (fun j ↦ ∫ z, f z ∂(μ (φ j))) atTop (𝓝 (∫ z, f z ∂V.measure))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
