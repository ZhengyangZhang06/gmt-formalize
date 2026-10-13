# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.polar_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. (Isometric parametrization.) Define the ℝ-linear map ι : Euclid 2 →ₗ[ℝ] Euclid P, ι v := v 0 • a + v 1 • e. For v ∈ Euclid 2: ‖ι v‖² = (v 0)²‖a‖² + 2 (v 0)(v 1)⟨a, e⟩ + (v 1)²‖e‖² = (v 0)² + (v 1)² (`norm_add_sq_real`, `norm_smul`, `real_inner_smul_left`, `real_inner_smul_right`, ⟨a, e⟩ = 0, ‖a‖ = ‖e‖ = 1), and ‖v‖² = (v 0)² + (v 1)² (`EuclideanSpace.norm_eq`, `Real.sq_sqrt`, `Fin.sum_univ_two`). Both norms are ≥ 0, so ‖ι v‖ = ‖v‖ (`pow_left_inj₀`), and an additive norm-preserving map is an isometry (`AddMonoidHomClass.isometry_of_norm`).
2. (ι⁻¹ N is Lebesgue-null.) `Isometry.euclideanHausdorffMeasure_preimage` gives μHE[2] (ι ⁻¹' N) = μHE[2] (N ∩ range ι) ≤ μHE[2] N = 0 (`measure_mono_null`, `Set.inter_subset_left`), and μHE[2] = volume on Euclid 2 (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2`). So volume (ι ⁻¹' N) = 0.
3. (Pass to ℝ × ℝ.) Let κ : ℝ × ℝ → Euclid 2, κ p := WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p); then κ p 0 = p.1 and κ p 1 = p.2 (`MeasurableEquiv.finTwoArrow_symm_apply`). κ is measure preserving volume → volume, as the composition of `(volume_preserving_finTwoArrow ℝ).symm` and `PiLp.volume_preserving_toLp (Fin 2)`. Hence (`MeasurePreserving.quasiMeasurePreserving`, `QuasiMeasurePreserving.preimage_null`) N₃ := κ ⁻¹' (ι ⁻¹' N) has volume 0. Choose a measurable N₃' ⊇ N₃ with volume N₃' = 0 (`exists_measurable_superset_of_null`).
4. (Polar coordinates.) `lintegral_comp_polarCoord_symm` applied to f := N₃'.indicator 1 gives ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) = ∫⁻ p, f p = volume N₃' = 0 (`lintegral_indicator_one`, N₃' measurable). The integrand is measurable (`ENNReal.measurable_ofReal.comp measurable_fst`, times the measurable indicator of N₃' composed with the continuous map polarCoord.symm, `continuous_polarCoord_symm`). By `lintegral_eq_zero_iff` it vanishes (volume.restrict polarCoord.target)-a.e.; polarCoord.target = Ioi 0 ×ˢ Ioo (−π) π is open, hence measurable, so `ae_restrict_iff'` gives: for volume-a.e. p, p ∈ polarCoord.target → ENNReal.ofReal p.1 • f (polarCoord.symm p) = 0.
5. (Conclusion.) Fix p as in Step 4 with 0 < p.1, −π < p.2 < π, so p ∈ polarCoord.target, and suppose p.1 • (cos p.2 • a + sin p.2 • e) ∈ N. Since polarCoord.symm p = (p.1 * cos p.2, p.1 * sin p.2) (`polarCoord_symm_apply`), ι (κ (polarCoord.symm p)) = (p.1 * cos p.2) • a + (p.1 * sin p.2) • e = p.1 • (cos p.2 • a + sin p.2 • e) (`smul_add`, `smul_smul`), so polarCoord.symm p ∈ N₃ ⊆ N₃'. Then the integrand at p is ENNReal.ofReal p.1 • 1 = ENNReal.ofReal p.1, which vanishes only if p.1 ≤ 0 (`ENNReal.ofReal_eq_zero`), contradicting 0 < p.1. Hence p.1 • (cos p.2 • a + sin p.2 • e) ∉ N. ∎

## Key steps

1. ι(v) = v₀a + v₁e is a linear isometry Euclid 2 → ℝ^P, so volume(ι⁻¹N) = μHE[2](N ∩ range ι) = 0.
2. κ : ℝ × ℝ → Euclid 2 (toLp ∘ finTwoArrow.symm) is measure preserving, so N₃ := κ⁻¹ι⁻¹N is Lebesgue-null; take a measurable null superset N₃'.
3. lintegral_comp_polarCoord_symm with the indicator of N₃': ∫_{target} ofReal(p₁)·1_{N₃'}(polarCoord.symm p) dp = 0, so the integrand vanishes a.e. on polarCoord.target.
4. On the target p₁ > 0, so polarCoord.symm p ∉ N₃', i.e. p₁(cos p₂·a + sin p₂·e) = ι(κ(polarCoord.symm p)) ∉ N.

## Reference use

### local-project

Queries:
- `python3 scans of dag.json: selected node; parent idtp_cone_sector_endpoint_density and its 11 children; statuses, types and candidate commits of dimred_im_mass_measure, imrep_represents_support_eq_inter_measure_support, idtp_imrep_measure_density_ae (decomposing), dtc_approxTangent_of_null_diff, dpf_itt_approxTangentPlane_eq, imrep_carrier_sdiff_support_null, rsd_massOn_eq_measure, rsd_ae_hasMassDensity_mult, dorag_sn_hausdorff_le_mul_of_lower_density, dorag_sn_open_superset_measure_lt, dimred_cs_mi_*, regcomp_atl_upper_density_zero, idtp_ccd_planar_support_mass`
- `regex scans of accepted DAG statements for polar|isometr|approxTangent|null_diff|plane, 'polarCoord'/'Real.cos', 'HasMassDensity' with 'R.mult'/'R.carrier', and '∉ R.carrier'`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for the 6 reused declarations (type byte-identity, sorry/axiom count); git merge-base --is-ancestor 591230fd 71a35e92`
- `precedent records: nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invariance-a1/decomposition-v1.json and nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-audit-v3.json`
- `name checks: dag.json lean_names; grep -rl idtp_cse_sp_ nodes/ local-references/; git log --all -S idtp_cse_sp_`
- `rg -n 'theorem lintegral_comp_polarCoord_symm|lemma isOpen_image_of_subset_source|theorem Isometry.euclideanHausdorffMeasure_preimage|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem volume_preserving_finTwoArrow|theorem PiLp.volume_preserving_toLp|theorem preimage_null|theorem exists_measurable_superset_of_null|theorem lintegral_eq_zero_iff |theorem finrank_span_eq_card|theorem eq_of_le_of_finrank_eq|theorem two_le_pi|theorem pi_gt_three' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'idtp_cse_sp_|polarCoord|HasApproximateTangentSpaceAt|approxTangentPlane|HasMassDensity' local-references/123e8435b4a2469b/project`
- `grep -n 'def HasApproximateTangentSpaceAt|theorem hasApproximateTangentSpaceAt_submodule|theorem HasApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `lake env lean /tmp/sp_check/v2/All_axiom.lean; lake env lean /tmp/sp_check/v2/All_sorry.lean; earlier probes /tmp/sp_check/Stmts.lean, Region.lean, Polar.lean, Sector.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Pi/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-64496f9e64/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invariance-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-audit-v3.json`
- `/tmp/sp_check/v2/All_axiom.lean`
- `/tmp/sp_check/v2/All_sorry.lean`
- `/tmp/sp_check/v2/subproblems.json`

Pins match: project b4d606db and mathlib 25730c7c. Every Mathlib and SimonGMT name cited by the new children exists at these pins. Real.pi_gt_three exists but GMT.Ch07.Submission does not import it, so Real.two_le_pi is used. No accepted DAG lemma covers polar-coordinate null sets, relative openness of the sector, or the flat-region statement, so those become new children. The external facts the supplied proof needs are supplied by six accepted declarations, reused at byte-identical types: rsd_massOn_eq_measure, rsd_ae_hasMassDensity_mult, dorag_sn_hausdorff_le_mul_of_lower_density, dorag_sn_open_superset_measure_lt, imrep_carrier_sdiff_support_null and dtc_approxTangent_of_null_diff. These replace the pending idtp_imrep_measure_density_ae (status decomposing, an ancestor dependency not exposed to this node), and dimred_im_mass_measure and dpf_itt_approxTangentPlane_eq are no longer needed. The four new names are unreserved. The v2 Lean check proves the four new children, and the parent at its exact frozen type, from these six declarations with standard axioms only.
