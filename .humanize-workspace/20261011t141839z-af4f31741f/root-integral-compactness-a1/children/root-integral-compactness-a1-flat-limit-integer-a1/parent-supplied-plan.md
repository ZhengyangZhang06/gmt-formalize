# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.flat_limit_integer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1`
- Child key: `flat_limit_integer`
- Declaration: `Submission.intcpt_flat_limit_integer_multiplicity`
- Exact Lean type: `AllardRectifiabilityTheorem → FirstRectifiabilityTheorem → MonotonicityFormula → (∀ (N n : ℕ) (L : ℝ), 0 < L → L ≤ 1 → ∀ (U : Set (Euclidean N)) (V : Varifold N n U) (P : Grassmannian N n), ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) → ∃ i, x ∈ Γ i) → ∀ (N n : ℕ) (P : Grassmannian N n) (θ₀ : ℝ) (W : ℕ → Varifold N n (ball (0 : Euclidean N) 5)), 0 < θ₀ → (∀ k, IsIntegral (W k)) → (∀ k, (W k).HasLocallyBoundedFirstVariation) → Tendsto (fun k ↦ variationMeasure (W k) (ball (0 : Euclidean N) 5)) atTop (𝓝 0) → (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ ball (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N n)) → Tendsto (fun k ↦ ∫ z, f z ∂(W k).measure) atTop (𝓝 (θ₀ * ∫ z, f z ∂(planeVarifoldMeasure P)))) → ∃ m : ℕ, θ₀ = m`

## Sibling prerequisites

- `root.integral_compactness-a1.integral_density-a1`
- `root.integral_compactness-a1.canonical_representation-a1`
- `root.integral_compactness-a1.allard_lemma-a1`
- `root.integral_compactness-a1.graph_fibre_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
