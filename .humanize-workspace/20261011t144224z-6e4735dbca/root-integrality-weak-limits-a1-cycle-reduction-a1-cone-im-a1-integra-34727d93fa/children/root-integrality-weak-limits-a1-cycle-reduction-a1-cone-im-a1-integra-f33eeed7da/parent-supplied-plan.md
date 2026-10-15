# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.param_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-f33eeed7da/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1`
- Child key: `param_fubini`
- Declaration: `Submission.iwl_cr_ci_ie_param_fubini`
- Exact Lean type: `∀ (P m : ℕ) (μ : Measure (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) m) (Φ : ℝ → Eucl P → Covector (Eucl P) m) (Ψ : Eucl P → Covector (Eucl P) m) (B : ℝ), SFinite μ → Integrable θ μ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Eucl P) m, |ξ x α| ≤ ‖α‖) → Continuous (fun p : ℝ × Eucl P => Φ p.1 p.2) → (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, ‖Φ s x‖ ≤ B) → (∀ (x : Eucl P) (v : Fin m → Eucl P), Ψ x v = ∫ s in (0 : ℝ)..1, Φ s x v) → ∫ s in (0 : ℝ)..1, ∫ x, θ x * ξ x (Φ s x) ∂μ = ∫ x, θ x * ξ x (Ψ x) ∂μ`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.nvector_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
