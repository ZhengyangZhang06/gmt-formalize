# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.mollified_lipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-d402a62e0a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child key: `mollified_lipschitz`
- Declaration: `Submission.codim1_rdo_dg_bvc_mollified_lipschitz`
- Exact Lean type: `∀ (n : ℕ) (ρ : Euclid n → ℝ), ContDiff ℝ 1 ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → ∃ L : ℝ, ∀ F : Set (Euclid n), MeasurableSet F → (∀ x, |∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y)| ≤ L) ∧ ∀ x x', |(∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y)) - ∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x' - y)| ≤ L * ‖x - x'‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
