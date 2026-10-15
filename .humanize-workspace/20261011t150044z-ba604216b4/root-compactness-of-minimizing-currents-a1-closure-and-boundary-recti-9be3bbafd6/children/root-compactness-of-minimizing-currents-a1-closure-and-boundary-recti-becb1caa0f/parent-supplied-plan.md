# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.translation-a1.smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-becb1caa0f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.translation-a1`
- Child key: `smooth_approx`
- Declaration: `Submission.cbr_ci_cp_tr_smooth_approx_of_continuous`
- Exact Lean type: `∀ (P : ℕ) (g : Euclid P → ℝ), Continuous g → HasCompactSupport g → ∃ (K : Set (Euclid P)) (C : ℝ) (u : ℕ → Euclid P → ℝ), IsCompact K ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k)) ∧ (∀ k x, x ∉ K → u k x = 0) ∧ (∀ k x, |u k x| ≤ C) ∧ ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (g x))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1.normalized_mollifier-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
