# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1.image_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-29ff19b91f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1`
- Child key: `image_split`
- Declaration: `Submission.dpf_raf_lintegral_image_eq_tsum_pieces`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (A : ℕ → Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), (∀ i, MeasurableSet (A i)) → (∀ i, A i ⊆ M) → Pairwise (fun i j => Disjoint (A i) (A j)) → μHE[n] (M \ ⋃ i, A i) = 0 → LipschitzWith Λ φ → Injective φ → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in φ '' M, g y ∂μHE[n] = ∑' i, ∫⁻ y in φ '' A i, g y ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
