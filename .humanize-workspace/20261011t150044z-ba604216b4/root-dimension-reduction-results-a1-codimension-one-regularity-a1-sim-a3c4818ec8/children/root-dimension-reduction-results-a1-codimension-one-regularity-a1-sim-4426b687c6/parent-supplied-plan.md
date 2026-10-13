# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.cone_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-4426b687c6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child key: `cone_measure`
- Declaration: `Submission.codim1_hcp_sc_cone_annuli_measure`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)), (0 : Euclid P) ∉ M → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ c : ℝ, 0 < c → μHE[m] (M ∩ sphere (0 : Euclid P) c) = 0) ∧ (∀ α : ℝ, -(m : ℝ) < α → ∫⁻ x in M ∩ ball (0 : Euclid P) 1, ENNReal.ofReal (‖x‖ ^ α) ∂μHE[m] ≠ ∞) ∧ (∀ β : ℝ, β < -(m : ℝ) → ∫⁻ x in M \ ball (0 : Euclid P) 1, ENNReal.ofReal (‖x‖ ^ β) ∂μHE[m] ≠ ∞)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
