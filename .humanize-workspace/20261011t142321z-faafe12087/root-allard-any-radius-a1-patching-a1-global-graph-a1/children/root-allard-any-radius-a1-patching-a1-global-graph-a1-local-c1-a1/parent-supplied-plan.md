# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.global_graph-a1.local_c1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1-local-c1-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1.global_graph-a1`
- Child key: `local_c1`
- Declaration: `Submission.arp_contDiffOn_of_local_C1_reps`
- Exact Lean type: `∀ {m k : ℕ} (u : Rn m → Rn k) (Ω : Set (Rn m)) (L : ℝ), IsOpen Ω → (∀ x₀ ∈ Ω, ∃ (ε : ℝ) (f : Rn m → Rn k), 0 < ε ∧ ContDiffOn ℝ 1 f (ball x₀ ε) ∧ ‖fderiv ℝ f x₀‖ ≤ L ∧ ∀ w ∈ ball x₀ ε ∩ Ω, u w = f w) → ContDiffOn ℝ 1 u Ω ∧ ∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ L`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
