# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1.uniform_of_equilipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2cd20e5b26/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1`
- Child key: `uniform_of_equilipschitz`
- Declaration: `Submission.cbr_ci_pw_mu_uniform_of_equilipschitz`
- Exact Lean type: `∀ (n : ℕ) (K : Set (Euclid n)) (F : ℕ → Euclid n → ℝ) (a L : ℝ), IsCompact K → (∀ x ∈ K, Tendsto (fun k => F k x) atTop (𝓝 a)) → (∀ᶠ k in atTop, ∀ x ∈ K, ∀ x' ∈ K, |F k x - F k x'| ≤ L * dist x x') → TendstoUniformlyOn F (fun _ => a) atTop K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
