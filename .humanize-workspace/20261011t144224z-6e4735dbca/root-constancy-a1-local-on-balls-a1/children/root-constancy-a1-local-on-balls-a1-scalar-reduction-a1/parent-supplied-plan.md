# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.local_on_balls-a1.scalar_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-scalar-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.local_on_balls-a1`
- Child key: `scalar_reduction`
- Declaration: `Submission.constancy_topForm_scalar_reduction`
- Exact Lean type: `∀ (m : ℕ) (U : Set (Eucl (m + 1))) (T : GeometricCurrentOn U (m + 1)), ∃ u : (Eucl (m + 1) → ℝ) → ℝ, (∀ ω : TestFormOn U (m + 1), T ω = u (fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)))) ∧ (∀ b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∃ ω : TestFormOn U (m + 1), ∀ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) = b x) ∧ (∀ a b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → u (a + b) = u a + u b) ∧ (∀ (c : ℝ) (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → u (c • a) = c * u a) ∧ (∀ (a : ℕ → Eucl (m + 1) → ℝ) (b : Eucl (m + 1) → ℝ) (K : Set (Eucl (m + 1))), IsCompact K → K ⊆ U → (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → (∀ k, tsupport (a k) ⊆ K) → tsupport b ⊆ K → (∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (a k) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → Tendsto (fun k => u (a k)) atTop (𝓝 (u b)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
