# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.local_to_global_im-a1.tau_congr_on_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-congr-on-open-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child key: `tau_congr_on_open`
- Declaration: `Submission.ltg_tau_congr_on_open`
- Exact Lean type: `∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (ξ ξ' : Eucl P → NVector (Eucl P) k) (V : Set (Eucl P)), IsOpen V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 → (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ x = θ' x ∧ ξ x = ξ' x) → ∀ ω : DifferentialForm (Eucl P) k, tsupport ω ⊆ V → tauAction k M θ ξ ω = tauAction k M' θ' ξ' ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
