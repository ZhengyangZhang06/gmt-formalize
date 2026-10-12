# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1.euler_ode_power-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1-euler-dilation-c1-a1-76df93f87c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1`
- Child key: `euler_ode_power`
- Declaration: `Submission.varifold_tangents_rh_edc_pow_of_hasDerivAt`
- Exact Lean type: `∀ (n : ℕ) (F : ℝ → ℝ), (∀ t : ℝ, 0 < t → HasDerivAt F ((n : ℝ) * F t / t) t) → ∀ s : ℝ, 0 < s → F s = s ^ n * F 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
