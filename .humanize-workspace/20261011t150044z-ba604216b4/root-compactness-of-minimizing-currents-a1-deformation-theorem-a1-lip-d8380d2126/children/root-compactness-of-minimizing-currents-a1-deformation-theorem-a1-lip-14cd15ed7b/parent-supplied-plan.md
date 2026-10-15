# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.pullback_limits-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-14cd15ed7b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child key: `pullback_limits`
- Declaration: `Submission.cmcdt_lpoh_pullback_limits`
- Exact Lean type: `∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' m : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)) (ω : TestFormOn (univ : Set (Euclid N')) m), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (β : ℕ → TestFormOn (univ : Set (Euclid (N + 1))) m) (ρ₁ ρ₀ : ℕ → TestFormOn (univ : Set (Euclid N)) m), (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₁ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₀ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid N)) m, IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → X.support ⊆ K → Tendsto (fun j => X (ρ₁ j)) atTop (𝓝 (lpush N N' m G X ω)) ∧ Tendsto (fun j => X (ρ₀ j)) atTop (𝓝 (lpush N N' m F X ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) m, IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (β j)) atTop (𝓝 (lpush (N + 1) N' m H Y ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (m + 1), IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j))) atTop (𝓝 (lpush (N + 1) N' (m + 1) H Y (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)))) ∧ ∀ (j : ℕ), ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∃ (p : Euclid N') (D : Euclid (N + 1) →L[ℝ] Euclid N'), (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = ((ω : DifferentialForm (Euclid N') m) p).compContinuousLinearMap D ∧ ‖D (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) ∧ ∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.smooth_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
