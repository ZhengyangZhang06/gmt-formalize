# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1.cell_chains_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-7bd1c9a402/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1`
- Child key: `cell_chains_finite`
- Declaration: `Submission.dor_lmb_fc_tb_cell_chains_finite`
- Exact Lean type: `∀ (P m : ℕ) (U K : Set (Euclid P)) (ρ : ℝ) (B : ℕ), 0 < ρ → IsCompact K → {X : GeometricCurrentOn U (m + 1) | ∃ (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (b : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ), (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)} ⊆ K) ∧ (∀ p ∈ s, (b p).natAbs ≤ B) ∧ ∀ ω : TestFormOn U (m + 1), X ω = ∑ p ∈ s, (b p : ℝ) * ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)}, (ω : DifferentialForm (Euclid P) (m + 1)) x (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) ∂μHE[m + 1]}.Finite`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
