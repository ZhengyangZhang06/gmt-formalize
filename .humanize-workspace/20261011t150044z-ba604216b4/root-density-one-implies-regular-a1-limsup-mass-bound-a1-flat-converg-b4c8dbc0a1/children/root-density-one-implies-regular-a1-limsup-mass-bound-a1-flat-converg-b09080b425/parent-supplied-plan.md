# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.projected_cells-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-b09080b425/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1`
- Child key: `projected_cells`
- Declaration: `Submission.dor_lmb_fc_dtop_projected_cell_integral`
- Exact Lean type: `∀ (N : ℕ) (ρ : ℝ) (p : Euclid (N + 1) →L[ℝ] Euclid N) (z : Fin (N + 1) → ℤ) (ι : Fin N → Fin (N + 1)), (∀ (y : Euclid (N + 1)) (i : Fin N), p y i = y (Fin.castSucc i)) → StrictMono ι → (Fin.last N ∈ Set.range ι → ∀ ω : DifferentialForm (Euclid N) N, ∫ y in {y : Euclid (N + 1) | ∀ i : Fin (N + 1), (i ∈ Set.range ι → ρ * z i ≤ y i ∧ y i ≤ ρ * (z i + 1)) ∧ (i ∉ Set.range ι → y i = ρ * z i)}, ω (p y) (fun k => p (EuclideanSpace.single (ι k) (1 : ℝ))) ∂μHE[N] = 0) ∧ (Fin.last N ∉ Set.range ι → (∀ ω : DifferentialForm (Euclid N) N, ∫ y in {y : Euclid (N + 1) | ∀ i : Fin (N + 1), (i ∈ Set.range ι → ρ * z i ≤ y i ∧ y i ≤ ρ * (z i + 1)) ∧ (i ∉ Set.range ι → y i = ρ * z i)}, ω (p y) (fun k => p (EuclideanSpace.single (ι k) (1 : ℝ))) ∂μHE[N] = ∫ x in {x : Euclid N | ∀ i : Fin N, ρ * z (Fin.castSucc i) ≤ x i ∧ x i ≤ ρ * (z (Fin.castSucc i) + 1)}, ω x (fun k => EuclideanSpace.single k (1 : ℝ)) ∂μHE[N]) ∧ ∀ x : Euclid N, (∀ i : Fin N, ρ * z (Fin.castSucc i) ≤ x i ∧ x i ≤ ρ * (z (Fin.castSucc i) + 1)) → ∃ y : Euclid (N + 1), (∀ i : Fin (N + 1), (i ∈ Set.range ι → ρ * z i ≤ y i ∧ y i ≤ ρ * (z i + 1)) ∧ (i ∉ Set.range ι → y i = ρ * z i)) ∧ p y = x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
