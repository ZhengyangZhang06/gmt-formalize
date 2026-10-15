# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.refined_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-5729b2ece3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Child key: `refined_pieces`
- Declaration: `Submission.dtc_bc_lc_pfi_refined_bilipschitz_pieces`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (φ : Euclid P → Euclid P), MeasurableSet M → CountablyRectifiable n M → Differentiable ℝ φ → ∃ (G : ℕ → Euclid n → Euclid P) (A : ℕ → Set (Euclid n)) (κ : ℕ → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (G j)) ∧ (∀ j, MeasurableSet (A j)) ∧ (∀ j, 0 < κ j) ∧ (∀ j, ∀ a ∈ A j, ∀ a' ∈ A j, κ j * ‖a - a'‖ ≤ ‖G j a - G j a'‖) ∧ (∀ j, ∀ a ∈ A j, DifferentiableAt ℝ (G j) a ∧ Injective (fderiv ℝ (G j) a)) ∧ (∀ j, MeasurableSet (G j '' A j)) ∧ (∀ j, G j '' A j ⊆ M) ∧ Pairwise (fun i j => Disjoint (G i '' A i) (G j '' A j)) ∧ μHE[n] (M \ ⋃ j, G j '' A j) = 0 ∧ ∀ j, ((∃ κ' : ℝ, 0 < κ' ∧ ∀ a ∈ A j, ∀ a' ∈ A j, κ' * ‖a - a'‖ ≤ ‖φ (G j a) - φ (G j a')‖) ∧ ∀ a ∈ A j, Injective (fderiv ℝ (φ ∘ G j) a)) ∨ ∀ a ∈ A j, ¬ Injective (fderiv ℝ (φ ∘ G j) a)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_pieces-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
