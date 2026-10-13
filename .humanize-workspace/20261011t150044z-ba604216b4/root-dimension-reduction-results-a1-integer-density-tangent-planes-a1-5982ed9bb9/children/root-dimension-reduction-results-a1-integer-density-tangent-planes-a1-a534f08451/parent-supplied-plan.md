# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.tangent_measures-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a534f08451/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child key: `tangent_measures`
- Declaration: `Submission.idtp_fons_cc_tangent_measures`
- Exact Lean type: `DensityAndTangentCones → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N G : Set (Euclid (n + k))) (T : GeometricCurrentOn U n) (R : IMRep U n) (p : Euclid (n + k)) (lams : ℕ → ℝ), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → R.Represents T → IsOpen G → p ∈ U → p ∈ G → (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RC : IMRep (univ : Set (Euclid (n + k))) n), StrictMono sub ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C ∧ RC.Represents C ∧ (∀ t : ℝ, 0 < t → ∀ w : Euclid (n + k), limsup (fun ρ : ℝ => RC.measure (ball (t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) = limsup (fun ρ : ℝ => RC.measure (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)) ∧ ∀ f : Euclid (n + k) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • (R.measure.restrict G).map (dilation p (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂RC.measure))) ∧ ∀ (n k : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (R : IMRep (univ : Set (Euclid (n + k))) n) (y : Euclid (n + k)) (lams : ℕ → ℝ), 1 ≤ n → IsMinimizingIn S univ → BoundaryVanishes S → R.Represents S → (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RC : IMRep (univ : Set (Euclid (n + k))) n), StrictMono sub ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C ∧ RC.Represents C ∧ (∀ t : ℝ, 0 < t → ∀ w : Euclid (n + k), limsup (fun ρ : ℝ => RC.measure (ball (t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) = limsup (fun ρ : ℝ => RC.measure (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)) ∧ ∀ f : Euclid (n + k) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • R.measure.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂RC.measure))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1`
- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.blowup_limit_cycle-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.ambient_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
