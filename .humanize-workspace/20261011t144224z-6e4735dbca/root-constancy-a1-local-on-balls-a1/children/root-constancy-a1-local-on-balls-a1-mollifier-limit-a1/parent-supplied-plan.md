# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.local_on_balls-a1.mollifier_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-mollifier-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.local_on_balls-a1`
- Child key: `mollifier_limit`
- Declaration: `Submission.constancy_local_of_mollified_const`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Eucl n)) (u : (Eucl n → ℝ) → ℝ), (∀ (a : ℕ → Eucl n → ℝ) (b : Eucl n → ℝ) (K : Set (Eucl n)), IsCompact K → K ⊆ U → (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → (∀ k, tsupport (a k) ⊆ K) → tsupport b ⊆ K → (∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (a k) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → Tendsto (fun k => u (a k)) atTop (𝓝 (u b))) → ∀ (x₀ : Eucl n) (ρ R : ℝ), 0 < ρ → closedBall x₀ R ⊆ U → ∀ (ψ : ℕ → Eucl n → ℝ) (r : ℕ → ℝ), (∀ k, Continuous (ψ k)) → (∀ k, tsupport (ψ k) ⊆ closedBall 0 (r k)) → (∀ k, 0 ≤ r k) → (∀ k, ρ + r k ≤ R) → (∀ b : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → ∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (convolution (ψ k) b (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → ∀ c : ℕ → ℝ, (∀ (k : ℕ) (f : Eucl n → ℝ), IntegrableOn f (ball x₀ ρ) volume → u (convolution (ψ k) ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = c k * ∫ x in ball x₀ ρ, f x ∂volume) → ∃ c₀ : ℝ, ∀ b : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ ball x₀ ρ → u b = c₀ * ∫ x, b x ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
