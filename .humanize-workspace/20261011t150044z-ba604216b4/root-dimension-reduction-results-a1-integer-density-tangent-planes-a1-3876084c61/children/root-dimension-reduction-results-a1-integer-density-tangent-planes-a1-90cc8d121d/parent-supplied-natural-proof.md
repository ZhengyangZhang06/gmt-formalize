# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.local_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1, 4 and 5 (chart, inverse function theorem, relative openness of the image), stated for a general transversal C¹ map F instead of F = (|x|, f(x)). Conventions: E₂ := Euclid 2; B_r(x) := ball x r; Q := span(tangentSpace M p); "C¹" means ContDiff(On/At) ℝ 1; Dg := fderiv ℝ g. A Lean proof file may add the proof-only import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff.
1. (Chart.) Apply IsEmbeddedSubmanifold 1 2 M at p: an open V₀ ⊆ E₂, an open W₀ ∋ p and ψ : E₂ → Euclid P that is C¹ on V₀, injective on V₀, with ψ(V₀) = W₀ ∩ M, V₀ ∩ ψ⁻¹(K) compact for every compact K ⊆ W₀, and Dψ(z) injective for z ∈ V₀. Choose v₀ ∈ V₀ with ψ(v₀) = p. By the accepted lemma Submission.chart_tangentSpace_eq_range_fderiv (d := 2, r := 1, N := M), tangentSpace M (ψ v) = Set.range Dψ(v) for every v ∈ V₀; in particular Set.range Dψ(v₀) = tangentSpace M p ⊆ Q.
2. (Pointwise regularity.) As V₀ and U are open, ψ is C¹ at every v ∈ V₀ and F is C¹ at every x ∈ U (ContDiffOn.contDiffAt); in particular both are differentiable there with derivatives Dψ(v), DF(x).
3. (The composite.) V₀′ := V₀ ∩ ψ⁻¹(U) is open (ψ is continuous on the open set V₀; ContinuousOn.isOpen_inter_preimage) and contains v₀. Φ := F ∘ ψ is C¹ on V₀′ (composition), hence C¹ at v₀ with DΦ(v₀) = DF(p) ∘ Dψ(v₀) (chain rule). DΦ(v₀) : E₂ → E₂ is injective: if DF(p)(Dψ(v₀)z) = 0, then Dψ(v₀)z ∈ tangentSpace M p ⊆ Q, so transversality gives Dψ(v₀)z = 0, and injectivity of Dψ(v₀) gives z = 0. An injective linear endomorphism of the finite-dimensional space E₂ is bijective, so DΦ(v₀) is the coercion of a continuous linear equivalence E₀ : E₂ ≃L[ℝ] E₂ (LinearEquiv.ofInjectiveEndo, then LinearEquiv.toContinuousLinearEquiv).
4. (Invertibility persists.) v ↦ DΦ(v) is continuous on the open set V₀′ (ContDiffOn.continuousOn_fderiv_of_isOpen), and the set of continuous linear maps that are coercions of continuous linear equivalences is open (ContinuousLinearEquiv.isOpen). Hence V₁′ := {v ∈ V₀′ : DΦ(v) is such a coercion} is open (ContinuousOn.isOpen_inter_preimage) and contains v₀.
5. (Inverse function theorem.) Φ is C¹ at v₀ with HasFDerivAt Φ E₀ v₀, so ContDiffAt.toOpenPartialHomeomorph (n = 1 ≠ 0) yields an open partial homeomorphism Φ̃ whose coercion is Φ and with v₀ ∈ Φ̃.source. Restrict it to the open set V₁′ (OpenPartialHomeomorph.restrOpen, source = Φ̃.source ∩ V₁′): this gives Φ₁ with open source V₁ ∋ v₀ (so V₁ ⊆ V₀, ψ(V₁) ⊆ U, and DΦ(v) is invertible for every v ∈ V₁) and open target O := Φ₁.target = Φ(V₁). Then Φ₁.symm maps O into V₁, Φ(Φ₁.symm w) = w for w ∈ O, Φ₁.symm(O) = V₁ (symm_image_target_eq_source), and F(p) = Φ(v₀) ∈ O.
6. (C¹ inverse.) Let w ∈ O, v := Φ₁.symm w ∈ V₁, and let E_v be the equivalence with DΦ(v) = E_v. Φ is C¹ at v with HasFDerivAt Φ E_v v, so OpenPartialHomeomorph.contDiffAt_symm (w ∈ Φ₁.target) shows that Φ₁.symm is C¹ at w, and OpenPartialHomeomorph.hasFDerivAt_symm gives HasFDerivAt Φ₁.symm E_v⁻¹ w; E_v⁻¹ is surjective.
7. (Definition of G.) Put G := ψ ∘ Φ₁.symm. For w ∈ O, ψ is C¹ at Φ₁.symm w ∈ V₀ and Φ₁.symm is C¹ at w, so G is C¹ at w; hence G is C¹ on O. F(G w) = (F ∘ ψ)(Φ₁.symm w) = Φ(Φ₁.symm w) = w. By the chain rule DG(w) = Dψ(v) ∘ E_v⁻¹ with v = Φ₁.symm w; since E_v⁻¹ is surjective, Set.range DG(w) = Set.range Dψ(v) = tangentSpace M (ψ v) = tangentSpace M (G w) by step 1. Finally G(O) = ψ(Φ₁.symm(O)) = ψ(V₁).
8. (ψ(V₁) is relatively open in M.) For each v ∈ V₁ choose ε_v > 0 with B_{ε_v}(v) ⊆ V₁, and, by the accepted lemma Submission.dsmc_chart_inverse_continuity (applied to V₀, W₀, ψ: ψ is continuous and injective on V₀, ψ(V₀) ⊆ W₀, and the properness of step 1), choose δ_v > 0 such that every v′ ∈ V₀ with ‖ψ(v′) − ψ(v)‖ < δ_v satisfies ‖v′ − v‖ < ε_v. Let N₀ := ⋃_{v ∈ V₁} (W₀ ∩ B_{δ_v}(ψ v)), an open set. Then M ∩ N₀ = ψ(V₁): if x ∈ M ∩ W₀ ∩ B_{δ_v}(ψ v), then x ∈ W₀ ∩ M = ψ(V₀), say x = ψ(v′) with v′ ∈ V₀, and ‖ψ(v′) − ψ(v)‖ < δ_v forces v′ ∈ B_{ε_v}(v) ⊆ V₁, so x ∈ ψ(V₁); conversely, for v ∈ V₁, ψ(v) ∈ ψ(V₀) = W₀ ∩ M and ψ(v) ∈ B_{δ_v}(ψ v).
9. (Conclusion.) Put N := N₀ ∩ U, an open subset of U. Since ψ(V₁) ⊆ U, M ∩ N = (M ∩ N₀) ∩ U = ψ(V₁) ∩ U = ψ(V₁) = G(O). As v₀ ∈ V₁, p = ψ(v₀) ∈ M ∩ N, so p ∈ N. Hence O, N are open, F(p) ∈ O, p ∈ N ⊆ U, G is C¹ on O, G(O) = M ∩ N, and F(G w) = w and tangentSpace M (G w) = Set.range DG(w) for every w ∈ O. ∎

## Key steps

1. Chart (V₀, W₀, ψ) at p; the accepted chart_tangentSpace_eq_range_fderiv identifies tangentSpace M (ψ v) with range Dψ(v).
2. Φ = F∘ψ is C¹ near v₀ and DΦ(v₀) = DF(p)∘Dψ(v₀) is injective by transversality, hence invertible, and it stays invertible on an open V₁′ ∋ v₀.
3. Inverse function theorem (ContDiffAt.toOpenPartialHomeomorph restricted to V₁′): Φ₁ : V₁ → O is a homeomorphism with C¹ inverse (contDiffAt_symm, hasFDerivAt_symm).
4. G := ψ∘Φ₁.symm is C¹ on O, F∘G = id on O, range DG(w) = range Dψ(Φ₁.symm w) = tangentSpace M (G w), and G(O) = ψ(V₁).
5. The accepted dsmc_chart_inverse_continuity makes ψ(V₁) = M ∩ N₀ for an open N₀; N := N₀ ∩ U gives G(O) = M ∩ N and p ∈ N.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'IsEmbeddedSubmanifold\|def tangentSpace\|tangentSpace' GMT/Ch07/Contract.lean; sed -n 200,300p GMT/Ch07/Contract.lean`
- `python3 -I scans of dag.json lean_statement for: arctan | deriv φ | Ioo with deriv and ∃ c | μHE[2] | areaJacobian | LinearMap.trace | starProjection | tangentSpace | cutoff (= 1 with IsCompact K and HasCompactSupport); lean_name lookups chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity, dsmc_chart_tangentSpace_eq_range, dsmc_chart_range_subset_tangentSpace, fvmb_trace_starProjection_comp_eq_sum_inner, dgcr_bwd_normal_cutoff, dgce_left_inverse_tangentSpace_eq_range, doragm_sab_cutoff_profile`
- `grep -c idtp_ccd_scsp dag.json; grep -rl idtp_ccd_scsp runs/.../nodes; grep -l idtp_ccd_scsp ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (all no match, also for each of the 10 proposed names)`
- `grep -rn 'toOpenPartialHomeomorph|exists_contDiff_support_eq_eq_one_iff|exists_contDiff_tsupport_subset|IsCompact.exists_cthickening_subset_open|ContinuousLinearEquiv.isOpen|OpenPartialHomeomorph.hasFDerivAt_symm|restrOpen|symm_image_target_eq_source|volume_preserving_finTwoArrow|EuclideanSpace.volume_preserving_|euclideanHausdorffMeasure_eq_volume|LinearMap.finrank_range_of_inj|IsPreconnected.subset_of_closure_inter_subset|Filter.EventuallyEq.fderiv_eq|ContDiffOn.continuousOn_fderiv_of_isOpen|setIntegral_eq_integral_of_forall_compl_eq_zero|integral_hasDerivAt_right|contDiff_one_iff_deriv|hasDerivAt_arctan|contDiffAt_norm|LinearIndependent.pair_iff' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'theorem integral_area_formula_of_injective_derivative|def areaJacobianAt|areaJacobianAt_eq_normDet|areaJacobianAt_eq_sqrt_det_gram|normDet_sq_eq_det_gram|theorem ae_eq_const_of_weak_coordinate_derivatives_zero|def WeakDerivativesZero' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{WeightedArea,Area,AreaParametrization,AreaCurve}.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `lake env lean /tmp/scsp_check/Probe.lean; Children.lean; Assembly.lean (#print axioms); Conservation.lean; Planarity.lean; Imports.lean; Names.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3876084c61/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3876084c61/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Connected/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/tmp/scsp_check/Children.lean`
- `/tmp/scsp_check/Assembly.lean`
- `/tmp/scsp_check/Conservation.lean`
- `/tmp/scsp_check/Planarity.lean`
- `/tmp/scsp_check/Imports.lean`
- `/tmp/scsp_check/Names.lean`

Pins match. The snapshot project_commit b4d606d equals workspace HEAD, mathlib 25730c7c equals .lake/packages/mathlib HEAD, and SimonGMT is at the lakefile pin 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

The child proofs use three accepted DAG lemmas (status accepted): chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity and fvmb_trace_starProjection_comp_eq_sum_inner.

No accepted DAG lemma states any child: no DAG statement mentions arctan, and there is no 1-D weak-derivative constancy lemma, cone area formula, or submanifold local-inverse lemma. The idtp_ccd_scsp_* names have no match in dag.json, in the run nodes, or in any worktree Submission.lean.

Pinned Mathlib supplies the lemmas the proofs cite, including:
- inverse function theorem: ContDiffAt.toOpenPartialHomeomorph; OpenPartialHomeomorph.restrOpen, contDiffAt_symm and hasFDerivAt_symm
- cutoffs: ContinuousLinearEquiv.isOpen, exists_contDiff_support_eq_eq_one_iff (reachable from the frozen imports), IsCompact.exists_cthickening_subset_open
- volume transport: EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, volume_preserving_finTwoArrow, InnerProductSpace.euclideanHausdorffMeasure_eq_volume
- integrals: integral_prod_mul, setIntegral_indicator, support_fderiv_subset
- trigonometry: Real.cos_arctan, Real.sin_arctan

These names do not exist and are not cited: HasFDerivAt.norm, EuclideanSpace.measurableEquiv, unprimed setIntegral_congr, and ContDiffBump.normed (unavailable without an extra import).

SimonGMT supplies integral_area_formula_of_injective_derivative (WeightedArea.lean), areaJacobianAt_eq_normDet with LinearMap.normDet_sq_eq_det_gram (or areaJacobianAt_eq_sqrt_det_gram), and ae_eq_const_of_weak_coordinate_derivatives_zero. Using them requires proof-only imports, which load together with GMT.Ch07.Submission.

Lean checks:
- All 10 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07.
- The parent's exact frozen type is proved from the 10 Submission.* stubs, with axioms propext, Classical.choice and Quot.sound, plus sorryAx only from the stubs.
- cone_conservation is proved from the test_field, cone_area and angle_curve stubs.
- arc_planarity is proved from the angle_curve stub.
