# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.density_lower_bound-a1.restricted_varifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-density-lower-bound-a1-restricted-varifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Child key: `restricted_varifold`
- Declaration: `Submission.varifold_tangents_dlb_exists_restricted_varifold`
- Exact Lean type: `∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μ : Measure (Euclidean N × Grassmannian N n)) (c : ℝ≥0∞), IsOpen Ω → c ≠ ∞ → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ Ω → μ (K ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞) → ∃ W : Varifold N n Ω, W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
