# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-567cec0764/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child key: `slice_identity`
- Declaration: `Submission.dtc_bc_lc_sl_slice_identity`
- Exact Lean type: `∀ (P m : ℕ) (RT : IMRep (univ : Set (Euclid P)) (m + 2)) (RB : IMRep (univ : Set (Euclid P)) (m + 1)) (Rs : ℝ → IMRep (univ : Set (Euclid P)) (m + 1)) (f : Euclid P → ℝ), Measurable f → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), LocallyIntegrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) (m + 1)))) → (∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) (m + 1)) = (b - a) * ((∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 2]) - ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1])) → ∀ᵐ t, ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), (Rs t).action (ω : DifferentialForm (Euclid P) (m + 1)) = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 2]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
