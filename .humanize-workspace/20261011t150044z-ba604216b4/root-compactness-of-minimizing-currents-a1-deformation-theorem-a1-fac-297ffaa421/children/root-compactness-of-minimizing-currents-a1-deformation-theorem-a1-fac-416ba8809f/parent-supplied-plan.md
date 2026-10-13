# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-416ba8809f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1`
- Child key: `chain_boundary`
- Declaration: `Submission.cmcdtfr_chain_boundary`
- Exact Lean type: `∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s', StrictMono p.1) ∧ ∀ γ : TestFormOn (univ : Set (Euclid P)) m, T.boundary γ = ∑ p ∈ s', (β' p : ℝ) * ∫ y in {y : Euclid m | ∀ i, 0 < y i ∧ y i < 1}, (γ : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
