# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-41deb81aa5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1`
- Child key: `existence`
- Declaration: `Submission.dph_lpf_existence`
- Exact Lean type: `(∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) ∧ (∀ S' : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S' ω))) → S' = S) ∧ S.mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ S.support ⊆ closure (G '' X.support))`

## Sibling prerequisites

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.current_criterion-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`
- `root.compactness_mass_bounds-a1.mass_bound-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
