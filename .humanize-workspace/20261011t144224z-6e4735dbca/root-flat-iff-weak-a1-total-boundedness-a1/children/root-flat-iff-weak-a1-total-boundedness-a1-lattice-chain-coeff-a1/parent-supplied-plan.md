# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child key: `lattice_chain_coeff`
- Declaration: `Submission.fiw_tb_lattice_chain_coeff`
- Exact Lean type: `∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ) (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc → ∀ F : LatticeFaceIndex (m + 1) N, β F ≠ 0 → latticeFace ρ F ⊆ Pc.support ∧ ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
