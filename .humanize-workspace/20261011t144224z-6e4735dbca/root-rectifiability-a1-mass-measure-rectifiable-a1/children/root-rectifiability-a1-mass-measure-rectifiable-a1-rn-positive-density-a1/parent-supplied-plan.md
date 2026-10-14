# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.mass_measure_rectifiable-a1.rn_positive_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1-rn-positive-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.mass_measure_rectifiable-a1`
- Child key: `rn_positive_density`
- Declaration: `Submission.rectifiability_rn_positive_real_density`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (ν μ : Measure X) (B : Set X), MeasurableSet B → SigmaFinite (ν.restrict B) → SigmaFinite μ → μ Bᶜ = 0 → μ ≪ ν → ∃ (M : Set X) (θ : X → ℝ), M ⊆ B ∧ MeasurableSet M ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ (∀ K : Set X, MeasurableSet K → μ K < ∞ → IntegrableOn θ (M ∩ K) ν) ∧ μ = (ν.restrict M).withDensity (fun x => ENNReal.ofReal (θ x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
