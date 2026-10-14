# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-03314b82bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child key: `mollified_uniform`
- Declaration: `Submission.cbr_ci_pw_mollified_tendstoUniformlyOn`
- Exact Lean type: `∀ (n : ℕ) (R s c Λ : ℝ) (φ : Euclid n → ℝ) (u : ℕ → Euclid n → ℝ), 0 < R → 0 < s → s < R → ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ ball 0 s → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → (∀ᶠ k in atTop, ∫ y in ball 0 (2 * R), |u k y| ≤ Λ) → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ ball 0 (2 * R) → Tendsto (fun k => ∫ y in ball 0 (2 * R), u k y * b y) atTop (𝓝 (c * ∫ y, b y))) → TendstoUniformlyOn (fun k x => ∫ y in ball 0 (2 * R), u k y * φ (x - y)) (fun _ => c * ∫ y, φ y) atTop (closedBall 0 R)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
