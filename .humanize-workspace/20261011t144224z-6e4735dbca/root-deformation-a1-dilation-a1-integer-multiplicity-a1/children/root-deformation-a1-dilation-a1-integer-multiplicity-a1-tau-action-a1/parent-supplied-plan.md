# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.dilation-a1.integer_multiplicity-a1.tau_action-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1-integer-multiplicity-a1-tau-action-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.dilation-a1.integer_multiplicity-a1`
- Child key: `tau_action`
- Declaration: `Submission.deformation_dilation_im_tauAction`
- Exact Lean type: `∀ (N k : ℕ) (ρ : ℝ) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) k) (ω : DifferentialForm (Eucl N) k), 0 < ρ → MeasurableEmbedding (fun x : Eucl N => ρ • x) → MeasurePreserving (fun x : Eucl N => ρ • x) (ENNReal.ofReal (ρ ^ k) • (μHE[k] : Measure (Eucl N))) (μHE[k] : Measure (Eucl N)) → tauAction k M θ ξ (fun x : Eucl N => ρ ^ k • ω (ρ • x)) = tauAction k ((fun x : Eucl N => ρ • x) '' M) (fun y : Eucl N => θ (ρ⁻¹ • y)) (fun y : Eucl N => ξ (ρ⁻¹ • y)) ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
