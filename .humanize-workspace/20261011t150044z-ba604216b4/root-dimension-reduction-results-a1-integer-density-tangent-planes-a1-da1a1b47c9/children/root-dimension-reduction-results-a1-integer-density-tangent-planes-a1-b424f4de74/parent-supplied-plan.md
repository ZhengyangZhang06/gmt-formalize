# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b424f4de74/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child key: `tilt_decay`
- Declaration: `Submission.idtp_cse_bml_tilt_excess_decay`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (m : ℕ) (β : Covector (Euclid P) 2), R.Represents C → β ![a, e] = 1 → (∀ᵐ x ∂R.measure, |R.orient x β| ≤ 1) → (∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C' : GeometricCurrentOn (univ : Set (Euclid P)) 2) (c : ℤ), StrictMono φ ∧ c.natAbs = m ∧ ConvergesWeakly (fun j => blowUp C a (lams (φ j)) (hlams (φ j)).ne') C' ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) 2, C' ω = (c : ℝ) * ∫ x in (Q : Set (Euclid P)), (ω : DifferentialForm (Euclid P) 2) x ![a, e] ∂μHE[2]) ∧ ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams (φ j))⁻¹ ^ 2 * ∫ x, g (dilation a (lams (φ j)) x) ∂R.measure) atTop (𝓝 ((m : ℝ) * ∫ x in (Q : Set (Euclid P)), g x ∂μHE[2]))) → Tendsto (fun s' : ℝ => (∫⁻ x in ball a (3 * s'), ENNReal.ofReal (1 - |R.orient x β|) ∂R.measure) / ENNReal.ofReal (s' ^ 2)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.subseq_criterion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
