# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.derivative_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-d2de0f35b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1`
- Child key: `derivative_estimate`
- Declaration: `Submission.dor_lmb_ret_derivative_estimate`
- Exact Lean type: `∀ (P d : ℕ) (O : Set (Euclid P)) (g : Euclid P → Euclid d) (ψ : Euclid d → Euclid P) (Q : Euclid d → (Euclid P →L[ℝ] Euclid P)) (x : Euclid P) (a b : ℝ), IsOpen O → x ∈ O → DifferentiableAt ℝ g x → DifferentiableAt ℝ ψ (g x) → DifferentiableAt ℝ Q (g x) → (∀ z ∈ O, Q (g z) (z - ψ (g z)) = 0) → (Q (g x)).comp (fderiv ℝ ψ (g x)) = fderiv ℝ ψ (g x) → ‖Q (g x)‖ ≤ 1 → 0 ≤ a → 0 ≤ b → ‖fderiv ℝ Q (g x)‖ ≤ a → (∀ w : Euclid d, ‖w‖ ≤ b * ‖fderiv ℝ ψ (g x) w‖) → a * b * ‖x - ψ (g x)‖ ≤ 1 / 2 → ‖fderiv ℝ (ψ ∘ g) x‖ ≤ 1 + 2 * (a * b) * ‖x - ψ (g x)‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
