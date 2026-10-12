# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.c1_holder_extension-a1.holder_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-c1-holder-extension-a1-h-047960399b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.c1_holder_extension-a1`
- Child key: `holder_extension`
- Declaration: `Submission.allard52_c1h_holder_extension`
- Exact Lean type: `∀ (n m k : ℕ) (F : Rn n → (Rn m →L[ℝ] Rn k)) (S Z : Set (Rn n)) (M R α : ℝ), 0 ≤ M → 0 < R → 0 < α → S ⊆ closure Z → (∀ x ∈ Z, ∀ y ∈ Z, hsNorm (F x - F y) ≤ M * (‖x - y‖ / R) ^ α) → ∃ g : Rn n → (Rn m →L[ℝ] Rn k), ContinuousOn g S ∧ (∀ x ∈ Z, g x = F x) ∧ ∀ x ∈ S, ∀ y ∈ S, hsNorm (g x - g y) ≤ M * (‖x - y‖ / R) ^ α`

## Sibling prerequisites

- `root.allard_regularity-a1.graph_campanato-a1.c1_holder_extension-a1.hs_norm_basics-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
