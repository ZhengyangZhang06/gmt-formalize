# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.diagonal_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-diagonal-blowup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1`
- Child key: `diagonal_blowup`
- Declaration: `Submission.intcpt_diagonal_integral_blowup`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U) (ξ : Euclidean N) (P : Grassmannian N n) (θ₀ c r : ℝ), Varifold.RadonConverges Vi V → (∀ i, IsIntegral (Vi i)) → (∀ i, (Vi i).HasLocallyBoundedFirstVariation) → HasTangentPlane V ξ P θ₀ → 0 < r → (∀ ρ : ℝ, 0 < ρ → ρ < r → liminf (fun i ↦ variationMeasure (Vi i) (closedBall ξ ρ)) atTop ≤ ENNReal.ofReal (c * ρ ^ n)) → ∃ W : ℕ → Varifold N n (ball (0 : Euclidean N) 5), (∀ k, IsIntegral (W k)) ∧ (∀ k, (W k).HasLocallyBoundedFirstVariation) ∧ Tendsto (fun k ↦ variationMeasure (W k) (ball (0 : Euclidean N) 5)) atTop (𝓝 0) ∧ ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ ball (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N n)) → Tendsto (fun k ↦ ∫ z, f z ∂(W k).measure) atTop (𝓝 (θ₀ * ∫ z, f z ∂(planeVarifoldMeasure P)))`

## Sibling prerequisites

- `root.integral_compactness-a1.rescaled_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
