# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.flat_limit_integer-a1.tilt_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1-tilt-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child key: `tilt_cutoff`
- Declaration: `Submission.intcpt_fli_tilt_cutoff_cc`
- Exact Lean type: `∀ (N n : ℕ) (P : Grassmannian N n) (χ : Euclidean N → ℝ), Continuous χ → HasCompactSupport χ → ∃ f : C_c(Euclidean N × Grassmannian N n, ℝ), (∀ (z : Euclidean N) (S : Grassmannian N n), f (z, S) = χ z * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖) ∧ tsupport f ⊆ tsupport χ ×ˢ (univ : Set (Grassmannian N n))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
