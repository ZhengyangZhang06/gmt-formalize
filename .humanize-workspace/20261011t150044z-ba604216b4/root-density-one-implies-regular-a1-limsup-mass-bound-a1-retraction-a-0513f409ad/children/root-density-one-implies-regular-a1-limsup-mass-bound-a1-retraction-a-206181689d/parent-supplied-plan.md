# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1.map_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-206181689d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1`
- Child key: `map_calculus`
- Declaration: `Submission.dor_lmb_ret_nc_map_calculus`
- Exact Lean type: `∀ (P d : ℕ) (E : Submodule ℝ (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (Q : Euclid d → (Euclid P →L[ℝ] Euclid P)) (v₀ : Euclid d), IsOpen V → v₀ ∈ V → ContDiffOn ℝ 1 ψ V → ContDiffOn ℝ 1 Q V → (∀ k ∈ E, Q v₀ k = 0) → ContDiffOn ℝ 1 (fun z : Euclid d × E => ψ z.1 + (z.2 : Euclid P) - Q z.1 (z.2 : Euclid P)) (V ×ˢ univ) ∧ HasFDerivAt (fun z : Euclid d × E => ψ z.1 + (z.2 : Euclid P) - Q z.1 (z.2 : Euclid P)) ((fderiv ℝ ψ v₀).comp (ContinuousLinearMap.fst ℝ (Euclid d) E) + E.subtypeL.comp (ContinuousLinearMap.snd ℝ (Euclid d) E)) (v₀, 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
