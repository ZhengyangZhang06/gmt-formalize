# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.sector_open-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. (Coordinates in Q.) The family ![a, e] is orthonormal (`orthonormal_iff_ite`, using ⟨a, a⟩ = ‖a‖² = 1, ⟨e, e⟩ = 1, ⟨a, e⟩ = ⟨e, a⟩ = 0), hence linearly independent. Its span is ≤ Q (`Submodule.span_le`; a, e ∈ Q) and has finrank 2 = finrank Q (`finrank_span_eq_card`), so Submodule.span ℝ (range ![a, e]) = Q (`Submodule.eq_of_le_of_finrank_eq`). For y ∈ Q, `Submodule.mem_span_range_iff_exists_fun` and `Fin.sum_univ_two` give y = c 0 • a + c 1 • e; taking inner products with a and e gives ⟨y, a⟩ = c 0, ⟨y, e⟩ = c 1. Hence y = ⟨y, a⟩ • a + ⟨y, e⟩ • e for every y ∈ Q.
2. (An open set of coordinates.) Let W := Ioi 0 ×ˢ Ioo 0 δ ⊆ ℝ × ℝ (open). Since δ ≤ π and 0 < π, Ioo 0 δ ⊆ Ioo (−π) π, so W ⊆ polarCoord.target = Ioi 0 ×ˢ Ioo (−π) π. polarCoord.symm is an OpenPartialHomeomorph with source polarCoord.target, so O := polarCoord.symm '' W is open (`OpenPartialHomeomorph.isOpen_image_of_subset_source`).
3. (Continuous coordinates.) Let c : Euclid P → ℝ × ℝ, c y := (⟨y, a⟩, ⟨y, e⟩); it is continuous. For x₀ := t • (cos φ • a + sin φ • e), expanding with `inner_add_left`, `real_inner_smul_left` and the orthonormality relations gives c x₀ = (t * cos φ, t * sin φ) = polarCoord.symm (t, φ) with (t, φ) ∈ W (0 < t, 0 < φ < δ). So x₀ ∈ c ⁻¹' O, which is open, and `Metric.isOpen_iff` gives r > 0 with ball x₀ r ⊆ c ⁻¹' O.
4. (Conclusion.) Let y ∈ Q with dist y x₀ < r. Then c y ∈ O: there is (t', φ') ∈ W, i.e. 0 < t' and 0 < φ' < δ, with (t' * cos φ', t' * sin φ') = polarCoord.symm (t', φ') = c y, i.e. ⟨y, a⟩ = t' cos φ' and ⟨y, e⟩ = t' sin φ'. By Step 1, y = ⟨y, a⟩ • a + ⟨y, e⟩ • e = (t' * cos φ') • a + (t' * sin φ') • e = t' • (cos φ' • a + sin φ' • e) (`smul_add`, `smul_smul`). ∎

## Key steps

1. (a, e) is an orthonormal basis of Q, so y = ⟨y, a⟩a + ⟨y, e⟩e for every y ∈ Q.
2. W = (0, ∞) × (0, δ) ⊆ polarCoord.target (δ ≤ π), so O := polarCoord.symm '' W is open.
3. c(y) = (⟨y, a⟩, ⟨y, e⟩) is continuous and c(x₀) = polarCoord.symm (t, φ) ∈ O, giving a ball B_r(x₀) ⊆ c⁻¹(O).
4. For y ∈ Q ∩ B_r(x₀), c(y) = (t' cos φ', t' sin φ') with (t', φ') ∈ W, hence y = t'(cos φ'·a + sin φ'·e).

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
