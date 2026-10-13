# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 7–10 and facts (b), (c), (e) of the parent proof of idtp_tdc_density_locally_constant, for one light point.
- The parent's z_i, k_i, δ_i and arc half-length r'/2 become z, k, δ and L.
- The parent's derivation of the endpoint hypothesis from 'a ∉ J' is replaced by hypothesis (H) below.
- The disc radius ρ := min(1/2, L/4) is the parent's ρ₀ = min(1/2, r'/8) with L = r'/2.
Hypotheses: C minimizing in ℝ^P, ∂C = 0, C a cone; z ∈ spt C, ‖z‖ = 1; k ≥ 1; δ > 0 with HasMassDensity C y k for all y ∈ spt C ∩ B_δ(z); L > 0.
(H): every a ∈ spt C with ‖a‖ = 1, a ∈ B_L(z) and HasMassDensity C a k has δ' > 0 and k' ∈ ℕ with HasMassDensity C y k' for all y ∈ spt C ∩ B_δ'(a).
0. Facts.
   - (b) The sibling Submission.idtp_tdc_dlc_subspace_eq_of_inter_ball_eq: x ∈ Q₁, t > 0 and Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x) imply Q₁ = Q₂.
   - (e) The sibling Submission.idtp_tdc_dlc_normalize_dist_le: y ≠ 0 and ‖w‖ = 1 imply ‖‖y‖⁻¹ • y − w‖ ≤ 2‖y − w‖.
   - (c) C is integer multiplicity (first component of IsMinimizingIn C univ). For s > 0, Submission.idtp_tdc_cone_dilation (P, 2, C, s) gives s • x ∈ spt C ↔ x ∈ spt C and HasMassDensity C (s • x) θ ↔ HasMassDensity C x θ, for all x and θ.
   - Good. For the subspace Q fixed in step 1 and w ∈ ℝ^P, Good(w) means: ∃ ε > 0 with spt C ∩ B_ε(w) = Q ∩ B_ε(w) and HasMassDensity C y k for every y ∈ spt C ∩ B_ε(w).
   - Restriction. If Good(w) holds with ε, it holds with every t ∈ (0, ε]. Intersect both sides of the set equation with B_t(w) ⊆ B_ε(w).
1. (The plane at z.) z ≠ 0, since ‖z‖ = 1. Apply the parent's prerequisite Submission.idtp_cone_constant_density_planar to P, C, p := z, k and δ. Its hypotheses are the three hypotheses on C, z ∈ spt C, z ≠ 0, 0 < δ and the density hypothesis. It gives δ₁ > 0 and a subspace Q with finrank ℝ Q = 2, z ∈ Q and spt C ∩ B_δ₁(z) = Q ∩ B_δ₁(z). Fix this Q; it is the subspace of the conclusion.
2. (An orthonormal basis (z, e) of Q.)
   - The line ℝ∙z has finrank 1 (finrank_span_singleton, z ≠ 0), and finrank Q = 2. If Q ≤ ℝ∙z then 2 ≤ 1 (Submodule.finrank_mono), which is false. So some u ∈ Q has u ∉ ℝ∙z.
   - Put v := u − ⟨z, u⟩ z ∈ Q. Then v ≠ 0, since otherwise u = ⟨z, u⟩ z ∈ ℝ∙z. Also ⟨z, v⟩ = ⟨z, u⟩ − ⟨z, u⟩‖z‖² = 0.
   - Put e := ‖v‖⁻¹ • v ∈ Q. Then ‖e‖ = 1 and ⟨z, e⟩ = 0. The same holds for −e ∈ Q.
   - (z, e) is orthonormal, hence linearly independent, and span{z, e} ≤ Q. Both have finrank 2, so span{z, e} = Q (Submodule.eq_of_le_of_finrank_eq).
   - Consequently every w ∈ Q satisfies w = ⟨w, z⟩ z + ⟨w, e⟩ e. Indeed d := w − ⟨w, z⟩ z − ⟨w, e⟩ e lies in Q = span{z, e} and has ⟨d, z⟩ = ⟨d, e⟩ = 0. Writing d = αz + βe gives ‖d‖² = α⟨d, z⟩ + β⟨d, e⟩ = 0, so d = 0.
3. (Arcs.) Let ϵ ∈ {e, −e}. Apply the sibling Submission.idtp_tdc_arc_continuation to P, C, Q, z, ϵ, k and L. Its hypotheses hold as follows.
   - The three hypotheses on C hold; finrank Q = 2; z ∈ Q; ϵ ∈ Q; ‖z‖ = 1; ‖ϵ‖ = 1; inner ℝ z ϵ = 0; 1 ≤ k.
   - (i) ε₀ := min(δ, δ₁) > 0 works. By restriction of step 1, spt C ∩ B_ε₀(z) = Q ∩ B_ε₀(z). Every y ∈ spt C ∩ B_ε₀(z) ⊆ B_δ(z) has HasMassDensity C y k.
   - (ii) Let 0 < φ < L and a := cos φ • z + sin φ • ϵ, with a ∈ spt C and HasMassDensity C a k. As z ⊥ ϵ are unit vectors, ‖a‖² = cos²φ + sin²φ = 1 and ‖a − z‖² = (cos φ − 1)² + sin²φ = 2 − 2 cos φ. Since 1 − φ²/2 ≤ cos φ (Real.one_sub_sq_div_two_le_cos), ‖a − z‖² ≤ φ². So ‖a − z‖ ≤ φ < L, i.e. a ∈ B_L(z). (H) now gives δ' > 0 and k' ∈ ℕ with HasMassDensity C y k' for all y ∈ spt C ∩ B_δ'(a), which is (ii).
   The sibling yields Good(cos φ • z + sin φ • ϵ) for every φ with 0 ≤ φ < L, for both ϵ = e and ϵ = −e.
4. (Unit vectors of Q near z are Good.) Let w ∈ Q with ‖w‖ = 1 and ‖w − z‖ < L/2.
   - Put α := ⟨w, z⟩ and β := ⟨w, e⟩. Then w = α z + β e by step 2, and α² + β² = ‖w‖² = 1, so −1 ≤ α ≤ 1.
   - Let θ := arccos α ∈ [0, π] (Real.arccos_nonneg, Real.arccos_le_pi). Then cos θ = α (Real.cos_arccos), and sin θ = √(1 − α²) = √(β²) = |β| (Real.sin_arccos, Real.sqrt_sq_eq_abs).
   - Let ϵ := e if β ≥ 0 and ϵ := −e if β < 0. In both cases sin θ • ϵ = β e, so w = cos θ • z + sin θ • ϵ.
   - ‖w − z‖² = ‖w‖² − 2⟨w, z⟩ + ‖z‖² = 2 − 2α = 2 − 2 cos θ = 4 sin²(θ/2), using cos θ = cos(2·(θ/2)) = 1 − 2 sin²(θ/2) (Real.cos_two_mul_eq_one_sub).
   - Since θ/2 ∈ [0, π/2], Jordan's inequality (Real.mul_le_sin) gives sin(θ/2) ≥ (2/π)(θ/2) = θ/π ≥ 0. Hence ‖w − z‖ = 2 sin(θ/2) ≥ 2θ/π.
   - Therefore θ ≤ (π/2)‖w − z‖ < (π/2)(L/2) = πL/4 ≤ L (Real.pi_le_four). Since 0 ≤ θ < L, step 3 for this ϵ gives Good(w).
   This is the parent's angle parametrization of step 9, φ := arg(α + iβ), written as |φ| = θ with the sign absorbed into ϵ = ±e.
5. (Every point of the disc is Good.) Put ρ := min(1/2, L/4) and let x ∈ Q ∩ B_ρ(z).
   - ‖x‖ ≥ ‖z‖ − ‖x − z‖ > 1 − 1/2 = 1/2, so x ≠ 0. Put s := ‖x‖ > 0 and w := s⁻¹ • x ∈ Q. Then ‖w‖ = 1.
   - By (e) with y := x and w := z, ‖w − z‖ ≤ 2‖x − z‖ < 2ρ ≤ L/2. So step 4 gives Good(w) with some ε > 0.
   - We claim Good(x) holds with s·ε > 0. For y ∈ ℝ^P we have ‖s⁻¹ • y − w‖ = s⁻¹‖y − x‖, so y ∈ B_{sε}(x) ⟺ s⁻¹ • y ∈ B_ε(w). Also y ∈ spt C ⟺ s⁻¹ • y ∈ spt C, by (c) with factor s⁻¹. And y ∈ Q ⟺ s⁻¹ • y ∈ Q, as Q is a subspace and s ≠ 0.
   - Hence y ∈ spt C ∩ B_{sε}(x) ⟺ s⁻¹ • y ∈ spt C ∩ B_ε(w) = Q ∩ B_ε(w) ⟺ y ∈ Q ∩ B_{sε}(x).
   - For y ∈ spt C ∩ B_{sε}(x), Good(w) gives HasMassDensity C (s⁻¹ • y) k. Then (c) with factor s and point s⁻¹ • y gives HasMassDensity C (s • (s⁻¹ • y)) k, i.e. HasMassDensity C y k.
6. (Mass bound.) Let x ∈ Q ∩ B_ρ(z), and let ε_x > 0 witness Good(x) (step 5).
   - x ∈ Q ∩ B_{ε_x}(x) = spt C ∩ B_{ε_x}(x), so x ∈ spt C; and x ≠ 0.
   - Apply Submission.idtp_cone_constant_density_planar to P, C, p := x, k and δ := ε_x, with the density hypothesis taken from Good(x). It gives δ₂ > 0 and a subspace Q₂ with spt C ∩ B_δ₂(x) = Q₂ ∩ B_δ₂(x) and C.massOn W = (k : ℝ≥0∞) · μHE[2](W ∩ Q₂) for every open W ⊆ B_δ₂(x).
   - Put t := min(ε_x, δ₂) > 0. By restriction, Q ∩ B_t(x) = spt C ∩ B_t(x) = Q₂ ∩ B_t(x). Since x ∈ Q, (b) gives Q = Q₂.
   - Then ε := t has all three required properties. spt C ∩ B_t(x) = Q ∩ B_t(x) and HasMassDensity C y k for y ∈ spt C ∩ B_t(x), by restriction of Good(x). For open W ⊆ B_t(x) ⊆ B_δ₂(x), μHE[2](W ∩ Q) = 1 · μHE[2](W ∩ Q) ≤ (k : ℝ≥0∞) · μHE[2](W ∩ Q) = C.massOn W, because 1 ≤ k.
7. Q satisfies finrank ℝ Q = 2 and z ∈ Q (step 1), and step 6 gives the required ε for every x ∈ Q ∩ B_{min(1/2, L/4)}(z). ∎

## Key steps

1. idtp_cone_constant_density_planar at z gives a plane Q ∋ z with spt C ∩ B_δ₁(z) = Q ∩ B_δ₁(z).
2. Gram–Schmidt gives a unit e ∈ Q with e ⊥ z. Then Q = span{z, e} and w = ⟨w,z⟩z + ⟨w,e⟩e for w ∈ Q.
3. idtp_tdc_arc_continuation along ϵ = ±e for angles in [0, L) makes every arc point Good. Its endpoint hypothesis follows from (H), since arc points are unit vectors with ‖a − z‖ ≤ φ < L.
4. A unit vector w ∈ Q with ‖w − z‖ < L/2 equals cos θ z + sin θ (±e) with θ = arccos⟨w,z⟩ ≤ (π/2)‖w − z‖ < L (Jordan's inequality and π ≤ 4), so w is Good.
5. Cone dilation (idtp_tdc_cone_dilation) and normalize_dist_le make every x ∈ Q ∩ B_{min(1/2, L/4)}(z) Good, with radius ‖x‖ε.
6. idtp_cone_constant_density_planar at x plus subspace_eq_of_inter_ball_eq give C.massOn W = k·H²(W ∩ Q) ≥ H²(W ∩ Q) for open W near x.

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca9016021f/parent-child-handoff.json; cat .../parent-supplied-plan.md (selected frozen type, sibling prerequisites cone_dilation / arc_continuation / no_infinite_planar_pieces)`
- `python3 scan of dag.json: frozen lean_statement and status of idtp_tdc_cone_dilation, idtp_tdc_arc_continuation, idtp_tdc_no_infinite_planar_pieces, idtp_tdc_subspace_ball_measure, idtp_cone_tangent_cone_planar, idtp_cone_constant_density_planar, idtp_cone_sector_endpoint_density, dimred_minimizing_monotonicity, dtc_density_usc, idtp_planar_cycle_eq_const_mul; depends_on of the parent two_dim_cone_density-a1 and grandparent integer_density_tangent_planes-a1`
- `python3 scan of dag.json lean_statements for density uniqueness ('HasMassDensity' with "θ = θ'"), plane uniqueness ('(Q₁ Q₂ : Submodule') and the normalization inequality ('‖y‖⁻¹ • y', '2 * ‖')`
- `python3 scan of dag.json lean_name prefix 'idtp_tdc_dlc' (974, then 979, then 1010 live nodes) and duplicate lean names; grep -rn idtp_tdc_dlc GMT .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (vs manifest.json)`
- `sed -n 1,457p GMT/Ch07/Contract.lean (HasMassDensity, IsConeCurrent, IsMinimizingIn, IsIntegerMultiplicity, BoundaryVanishes, IsEmbeddedSubmanifold, blowUp)`
- `rg -n "theorem isBounded_range_of_tendsto|def Infinite.natEmbedding|theorem Finite.preimage'|theorem mul_le_sin |theorem cos_arg|theorem sin_arg|theorem neg_pi_lt_arg|theorem arg_le_pi |theorem upperSemicontinuousOn_univ_iff|theorem finrank_span_singleton|theorem Orthonormal.linearIndependent|theorem finrank_euclideanSpace_fin|theorem norm_smul_inv_norm" mathlib/Mathlib`
- `rg -n "closed_of_finiteDimensional|lemma sin_le |one_sub_sq_div_two_le_cos|abs_sin_le_abs|pi_le_four|cos_two_mul_eq_one_sub|eq_of_le_of_finrank_eq|isBounded_iff_forall_norm_le|Infinite.exists_gt|fintype_card_le_finrank|ofReal_eq_ofReal_iff|tendsto_nhds_unique " mathlib/Mathlib`
- `lake env lean /tmp/dlc-split-a1/gen/Names.lean (#check of the 35 Mathlib names cited by the child proofs)`
- `lake env lean /tmp/dlc-split-a1/gen/Child_<key>.lean for the 5 children; lake env lean /tmp/dlc-split-a1/gen/Assembly.lean (#print axioms dlc_assembly_check); lake env lean /tmp/dlc-split-a1/agents/{small,cone_density_function,light_disc,accumulating_discs}/Check.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca9016021f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca9016021f/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Lattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Interval/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/tmp/dlc-split-a1/gen/children.json`
- `/tmp/dlc-split-a1/gen/Assembly.lean`
- `/tmp/dlc-split-a1/gen/Names.lean`
- `/tmp/dlc-split-a1/agents/small/Check.lean`
- `/tmp/dlc-split-a1/agents/cone_density_function/Check.lean`
- `/tmp/dlc-split-a1/agents/light_disc/Check.lean`
- `/tmp/dlc-split-a1/agents/accumulating_discs/Check.lean`

Pins and contract:
- Workspace HEAD b4d606db, mathlib 25730c7c and simongmt 2b366308 match manifest.json.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Namespace GMT.Ch07; opens Filter Function Set MeasureTheory Metric, scoped ENNReal Topology, Poincare.SimonGMT.Chapter06.

Reuse:
- Fact (a) of the supplied proof (density uniqueness) is exactly the accepted DAG declaration dimred_cs_mi_hasMassDensity_unique, with an identical frozen type. It is cited, with a short inline fallback proof, rather than re-proposed.
- No DAG node has the type of plane uniqueness, the normalization inequality, or the three packaged proof segments. So five new idtp_tdc_dlc_* names are used.
- None of these names occurs among the 1010 live DAG nodes, the node JSON files, or the workspace GMT sources.
- All seven cross-branch or sibling black boxes cited by the children (idtp_tdc_cone_dilation, idtp_tdc_arc_continuation, idtp_tdc_no_infinite_planar_pieces, idtp_cone_tangent_cone_planar, idtp_cone_constant_density_planar, dimred_minimizing_monotonicity, dimred_cs_mi_hasMassDensity_unique) are already cited by the supplied proof or by its fact (a).

Mathlib snapshot: it contains every lemma the child proofs cite. All 35 cited names #check successfully, including Real.mul_le_sin, Real.one_sub_sq_div_two_le_cos, Real.cos_arccos/sin_arccos, Real.pi_le_four, Set.Infinite.natEmbedding, Set.Finite.preimage', Metric.isBounded_range_of_tendsto and Submodule.closed_of_finiteDimensional.

Lean checks:
- All five lean_statements elaborate after import GMT.Ch07.Submission.
- The hypothesis-only assembly derives the exact selected type idtp_tdc_density_locally_constant. Axioms: propext, Classical.choice, Quot.sound.
- Each child is proved in Lean from the frozen types of the black boxes its natural proof cites, with the same axioms. Statement blocks were verified byte-identical to freshly generated templates.
