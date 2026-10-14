# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-weak-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1`
- Child key: `weak_identity`
- Declaration: `Submission.constancy_mdc_weak_partials_vanish`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Eucl n)) (u : (Eucl n → ℝ) → ℝ), (∀ a : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ∀ j : Fin n, u (fun x => fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ))) = 0) → ∀ (x₀ : Eucl n) (ρ ε : ℝ), closedBall x₀ (ρ + ε) ⊆ U → ∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ closedBall 0 ε → ∀ θ : Eucl n → ℝ, (∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume → u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = ∫ x in ball x₀ ρ, f x * θ x ∂volume) → ∀ a : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ ball x₀ ρ → ∀ j : Fin n, ∫ x, θ x * fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ)) ∂volume = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
