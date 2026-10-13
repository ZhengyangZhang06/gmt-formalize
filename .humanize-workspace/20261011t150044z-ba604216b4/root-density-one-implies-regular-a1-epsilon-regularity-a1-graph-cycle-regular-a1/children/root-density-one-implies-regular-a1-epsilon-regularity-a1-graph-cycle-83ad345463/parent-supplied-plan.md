# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-83ad345463/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child key: `integer_density`
- Declaration: `Submission.dgcr_graph_integer_density_on_graph`
- Exact Lean type: `∀ (n k : ℕ) (U : Set (Euclid (n + k))) (T : GeometricCurrentOn U n) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s h : ℝ) (ξ : Euclid (n + k) → MultiVector (n + k) n) (β : Euclid (n + k) → Covector (Euclid (n + k)) n), 0 < n → R.Represents T → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → 0 < h → ContDiffOn ℝ 1 u (ball 0 s) → {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → R.measure.support ∩ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} = (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s → ContinuousOn β ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) → (∀ x ∈ (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, ξ x (β x) = 1) → (∀ v ∈ ball (0 : Euclid n) s, IsUnitOrientationOf (ξ (z + ι v + ι' (u v))) (LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v : Euclid n →ₗ[ℝ] Euclid (n + k)))) → ∃ g : Euclid (n + k) → ℝ, LocallyIntegrableOn (fun v => g (z + ι v + ι' (u v))) (ball (0 : Euclid n) s) volume ∧ (∀ᵐ v ∂(volume.restrict (ball (0 : Euclid n) s)), ∃ m : ℤ, g (z + ι v + ι' (u v)) = m) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid (n + k)) n) ⊆ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} → T ω = ∫ x in (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, g x * ξ x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n]`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.orthogonal_coordinates-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_measure_bounds-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
