# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.linearity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-e7ea8f6410/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1`
- Child key: `linearity`
- Declaration: `Submission.dph_lpf_linearity`
- Exact Lean type: `(∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) → (∀ (m m' k : ℕ) (X X₁ X₂ : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (S S₁ S₂ : GeometricCurrentOn (univ : Set (Eucl m')) k) (a a₁ : ℝ), 0 < r → LipschitzOnWith Λ G (thickening r (X.support ∪ X₁.support)) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ (X.support ∪ X₁.support))) → (∀ ω, X₂ ω = a * X ω + a₁ * X₁ ω) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₁.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₁.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X₁ (ηj n)) atTop (𝓝 (S₁ ω))) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₂.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₂.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X₂ (ηj n)) atTop (𝓝 (S₂ ω))) → ∀ ω, S₂ ω = a * S ω + a₁ * S₁ ω)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
