# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.face_regroup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-bd3d9e9fe6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child key: `face_regroup`
- Declaration: `Submission.cmcdtfrcb_face_regroup`
- Exact Lean type: `∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ q ∈ s', StrictMono q.1) ∧ ∀ I : (Fin m → Fin P) × (Fin P → ℤ) → ℝ, ∑ p ∈ s, (β p : ℝ) * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (I (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1) - I (p.1 ∘ Fin.succAbove i, p.2)) = ∑ q ∈ s', (β' q : ℝ) * I q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
