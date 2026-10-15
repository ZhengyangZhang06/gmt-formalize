# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.minimizing_and_measures-a1.measure_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-minimizing-an-9d8328e359/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.minimizing_and_measures-a1`
- Child key: `measure_bounds`
- Declaration: `Submission.dtc_bc_mm_measure_bounds`
- Exact Lean type: `∀ (P n : ℕ) (Us : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ j, IsOpen (Us j)) → (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ Us j) → ConvergesWeakly Ss C → (∀ (K : Set (Euclid P)) (ε : ℝ), IsCompact K → 0 < ε → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ W : Set (Euclid P), IsOpen W ∧ K ⊆ W ∧ W ⊆ thickening ε K ∧ ∃ φ' : ℕ → ℕ, StrictMono φ' ∧ ∀ S : GeometricCurrentOn (univ : Set (Euclid P)) n, IsIntegerMultiplicity S → SameBoundary S C → (S - C).support ⊆ K → limsup (fun j => (Ss (ψ (φ' j))).massOn W) atTop ≤ S.massOn W) → ∀ Rs : (j : ℕ) → IMRep (Us j) n, (∀ j, (Rs j).Represents (Ss j)) → ∀ R : IMRep (univ : Set (Euclid P)) n, R.Represents C → (∀ K : Set (Euclid P), IsCompact K → R.measure K < ∞) ∧ (∀ K : Set (Euclid P), IsCompact K → limsup (fun j => (Rs j).measure K) atTop ≤ R.measure K) ∧ (∀ G : Set (Euclid P), IsOpen G → Bornology.IsBounded G → R.measure G ≤ liminf (fun j => (Rs j).measure G) atTop)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_equals_rep_measure-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.minimizing_and_measures-a1.mass_lsc-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.minimizing_and_measures-a1.limsup_criterion-a1`
- `root.regular_set_dense-a1.density_eq_multiplicity-a1.imrep_local_finiteness-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
