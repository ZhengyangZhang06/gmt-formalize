# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.local_on_balls-a1.mollified_l1_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-mollified-l1-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.local_on_balls-a1`
- Child key: `mollified_l1_bound`
- Declaration: `Submission.constancy_mollified_functional_l1_bounded`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Eucl n)) (u : (Eucl n → ℝ) → ℝ), (∀ a b : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → u (a + b) = u a + u b) → (∀ (c : ℝ) (a : Eucl n → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → u (c • a) = c * u a) → (∀ (a : ℕ → Eucl n → ℝ) (b : Eucl n → ℝ) (K : Set (Eucl n)), IsCompact K → K ⊆ U → (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → (∀ k, tsupport (a k) ⊆ K) → tsupport b ⊆ K → (∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (a k) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → Tendsto (fun k => u (a k)) atTop (𝓝 (u b))) → ∀ (x₀ : Eucl n) (ρ ε : ℝ), 0 < ρ → 0 < ε → closedBall x₀ (ρ + ε) ⊆ U → ∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ closedBall 0 ε → (∀ q : ℕ, ∃ C : ℝ, ∀ g : Eucl n → ℝ, Integrable g volume → ∀ x : Eucl n, ‖iteratedFDeriv ℝ q (convolution φ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ C * ∫ y, |g y| ∂volume) → (∀ f g : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume → IntegrableOn g (ball x₀ ρ) volume → u (convolution φ ((ball x₀ ρ).indicator (f + g)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) + u (convolution φ ((ball x₀ ρ).indicator g) (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ∧ (∀ (c : ℝ) (f : Eucl n → ℝ), IntegrableOn f (ball x₀ ρ) volume → u (convolution φ ((ball x₀ ρ).indicator (c • f)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = c * u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ∧ ∃ C : ℝ, ∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume → |u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume)| ≤ C * ∫ x in ball x₀ ρ, |f x| ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
