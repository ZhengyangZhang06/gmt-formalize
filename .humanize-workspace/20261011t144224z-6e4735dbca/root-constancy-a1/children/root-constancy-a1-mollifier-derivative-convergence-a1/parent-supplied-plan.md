# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.mollifier_derivative_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-mollifier-derivative-convergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1`
- Child key: `mollifier_derivative_convergence`
- Declaration: `Submission.constancy_approx_identity_iteratedFDeriv_tendstoUniformly`
- Exact Lean type: `∀ (n : ℕ) (b : Eucl n → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → ∀ (ψ : ℕ → Eucl n → ℝ) (r : ℕ → ℝ), (∀ k, Continuous (ψ k)) → (∀ k x, 0 ≤ ψ k x) → (∀ k, ∫ x, ψ k x ∂volume = 1) → (∀ k, tsupport (ψ k) ⊆ closedBall 0 (r k)) → Tendsto r atTop (𝓝 0) → ∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (convolution (ψ k) b (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) (fun x => iteratedFDeriv ℝ q b x) atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
