# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.source_charts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-source-charts-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child key: `source_charts`
- Declaration: `Submission.lpf_pi_source_charts`
- Exact Lean type: `((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → (∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0) → (∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' M)), HasWeightedApproximateTangentSpaceAt n M θ (Φ w) (LinearMap.range (fderiv ℝ Φ w).toLinearMap) ∧ HasFDerivAt (f ∘ Φ) ((L (Φ w)).comp (fderiv ℝ Φ w)) w) → (∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → ∃ (G : ℕ → Eucl n → Eucl Q) (O E : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ (∀ k, MeasurableSet (E k)) ∧ (∀ k, E k ⊆ O k ∩ Ω) ∧ Pairwise (Function.onFun Disjoint E) ∧ (∀ k, ∀ w ∈ E k, u w = G k w ∧ HasFDerivAt u (fderiv ℝ (G k) w) w) ∧ ∀ᵐ w ∂(volume : Measure (Eucl n)), w ∈ Ω → (∃ D : Eucl n →L[ℝ] Eucl Q, HasFDerivAt u D w ∧ Function.Injective D) → w ∈ ⋃ k, E k) → ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → ∃ (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), nVectorPushforward n (L x) (ξ x) ≠ 0 → ∃ k, ∃ w ∈ O k, G k w = f x ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧ Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧ (nVectorPushforward n (L x) (ξ x) = ‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ ∨ nVectorPushforward n (L x) (ξ x) = -(‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.induced_orientation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
