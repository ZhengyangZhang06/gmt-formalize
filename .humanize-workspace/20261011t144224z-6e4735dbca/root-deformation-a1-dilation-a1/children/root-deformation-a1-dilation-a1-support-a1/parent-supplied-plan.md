# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.dilation-a1.support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1-support-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.dilation-a1`
- Child key: `support`
- Declaration: `Submission.deformation_dilation_support`
- Exact Lean type: `∀ (N : ℕ) (ρ : ℝ), 0 < ρ → ∀ k : ℕ, ∀ X Y : GeometricCurrentOn (univ : Set (Eucl N)) k, (∀ ω η : TestFormOn (univ : Set (Eucl N)) k, (∀ x, (η : DifferentialForm (Eucl N) k) x = ρ ^ k • (ω : DifferentialForm (Eucl N) k) (ρ • x)) → Y ω = X η) → Y.support = (fun x => ρ • x) '' X.support`

## Sibling prerequisites

- `root.deformation-a1.dilation-a1.calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
