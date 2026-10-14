# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1.tangential_cutoff_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1-7e70544597/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1`
- Child key: `tangential_cutoff_field`
- Declaration: `Submission.mcs_exists_c1_field_eq_proj_near`
- Exact Lean type: `∀ (P : ℕ) (U N O : Set (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)) (X : Euclid P → Euclid P), IsOpen U → IsOpen O → N ⊆ O → ContDiffOn ℝ 1 pr O → (closure N \ N) ∩ U = ∅ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∃ XT : Euclid P → Euclid P, ContDiff ℝ 1 XT ∧ HasCompactSupport XT ∧ tsupport XT ⊆ U ∧ ∀ x ∈ N, XT =ᶠ[𝓝 x] (fun y => pr y (X y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
