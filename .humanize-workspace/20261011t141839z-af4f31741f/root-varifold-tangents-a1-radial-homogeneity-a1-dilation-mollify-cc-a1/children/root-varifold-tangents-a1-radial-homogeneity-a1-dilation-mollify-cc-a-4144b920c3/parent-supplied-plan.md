# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1.mollifier_c1_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1-dilation-mollify-cc-a-4144b920c3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1`
- Child key: `mollifier_c1_approx`
- Declaration: `Submission.varifold_tangents_rh_mc_exists_c1_approx`
- Exact Lean type: `∀ (N : ℕ) (g : Euclidean N → ℝ), Continuous g → HasCompactSupport g → ∃ (K : Set (Euclidean N)) (φ : ℕ → Euclidean N → ℝ), IsCompact K ∧ (∀ y ∉ K, g y = 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, ∀ y ∉ K, φ k y = 0) ∧ (∀ ε > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ y, |φ k y - g y| ≤ ε)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
