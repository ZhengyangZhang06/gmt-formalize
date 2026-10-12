# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.restrict_sigma_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-restrict-sigma-finite-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1`
- Child key: `restrict_sigma_finite`
- Declaration: `Submission.intcpt_id_restrict_sigmaFinite`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (U M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsOpen U → M ⊆ U → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) μ) → SigmaFinite (μ.restrict M)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
