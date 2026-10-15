# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.flat_region-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation and used results. H^n := μHE[n]; M := R.carrier; θ := R.mult; spt C := C.support; (hG) is the hypothesis on G. Siblings: density_mult = Submission.idtp_cse_sp_density_mult_ae (R.Represents C → ∀ᵐ y ∂μHE[n], ∀ k : ℕ, 1 ≤ k → HasMassDensity C y k → y ∈ R.carrier ∧ R.mult y = k); reuse child carrier_support_null = Submission.imrep_carrier_sdiff_support_null (IsOpen U → R.Represents T → μHE[n] (R.carrier \ T.support) = 0); reuse child approx_tangent_null_diff = Submission.dtc_approxTangent_of_null_diff (M' ⊆ M → IsOpen V → x ∈ V → μHE[n] ((M \ M') ∩ V) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q). From the SimonGMT library of the frozen contract: `Poincare.SimonGMT.Chapter03.hasApproximateTangentSpaceAt_submodule` (finrank ℝ Q = n → x ∈ Q → HasApproximateTangentSpaceAt n (Q : Set _) x Q) and `HasApproximateTangentSpaceAt.unique` (Simon Ch. 3, Remark 1.5(1)).
1. (Membership and multiplicity a.e. on G.) density_mult applied to (P, n, C, R, hR) gives: for H^n-a.e. y, every k' ≥ 1 with HasMassDensity C y k' satisfies y ∈ M ∧ θ y = k'. For y ∈ G, (hG) gives HasMassDensity C y k with 1 ≤ k. Hence (E1): for H^n-a.e. y, y ∈ G → (y ∈ M ∧ θ y = k).
2. (G \ M is H^n-null.) By `ae_iff`, E1 says H^n {y | ¬(y ∈ G → y ∈ M ∧ θ y = k)} = 0. Every y ∈ G \ M lies in this set (y ∈ G but y ∉ M). By `measure_mono_null`, (E2): H^n (G \ M) = 0.
3. (Approximate tangent planes a.e. on M.) The structure field R.orients says: for (H^n.restrict M)-a.e. y there is T with HasApproximateTangentSpaceAt n M y T (and an orientation property, which is discarded). As M is measurable (R.measurableSet_carrier), `ae_restrict_iff'` turns this into (E3): for H^n-a.e. y, y ∈ M → ∃ T, HasApproximateTangentSpaceAt n M y T.
4. (M lies a.e. in spt C.) carrier_support_null applied to (P, n, univ, C, R, isOpen_univ, hR) gives (E4): H^n (M \ spt C) = 0.
5. (Pointwise argument.) Combine E1 and E3 (filter_upwards), fix y satisfying both, and assume y ∈ G. By E1, y ∈ M and θ y = k; by E3 choose T with HasApproximateTangentSpaceAt n M y T. By (hG), y ∈ Q and there is r > 0 with Q ∩ ball y r ⊆ G and spt C ∩ ball y r ⊆ Q. Let V := ball y r (open, and y ∈ V because r > 0) and M' := M ∩ Q.
   (i) (M \ M') ∩ V ⊆ M \ spt C: if z ∈ M, z ∉ M ∩ Q, z ∈ V and z ∈ spt C, then z ∈ spt C ∩ ball y r ⊆ Q, so z ∈ M ∩ Q, a contradiction. By E4 and `measure_mono_null`, H^n ((M \ M') ∩ V) = 0. approx_tangent_null_diff applied to (P, n, M, M', V, y, T) with M' ⊆ M (`Set.inter_subset_left`), V open and y ∈ V yields HasApproximateTangentSpaceAt n M' y T.
   (ii) (Q \ M') ∩ V ⊆ G \ M: if z ∈ Q, z ∉ M ∩ Q and z ∈ V, then z ∈ Q ∩ ball y r ⊆ G, and z ∉ M (otherwise z ∈ M ∩ Q). By E2, H^n ((Q \ M') ∩ V) = 0. `hasApproximateTangentSpaceAt_submodule` (finrank ℝ Q = n, y ∈ Q) gives HasApproximateTangentSpaceAt n (Q : Set (Euclid P)) y Q, and approx_tangent_null_diff applied to (P, n, Q, M', V, y, Q) with M' ⊆ Q (`Set.inter_subset_right`) yields HasApproximateTangentSpaceAt n M' y Q.
   (iii) `HasApproximateTangentSpaceAt.unique` applied to (i) and (ii) gives T = Q, so HasApproximateTangentSpaceAt n M y Q. By definition approxTangentPlane n M y = if h : ∃ Q', HasApproximateTangentSpaceAt n M y Q' then h.choose else ⊥; the condition holds (witness Q), so approxTangentPlane n M y = h.choose (`dite_eq_left`, the non-deprecated name of `dif_pos` on this toolchain), and h.choose_spec with `HasApproximateTangentSpaceAt.unique` gives h.choose = Q.
   Hence y ∈ M ∧ θ y = k ∧ approxTangentPlane n M y = Q for H^n-a.e. y ∈ G. ∎

## Key steps

1. density_mult and the density hypothesis: Hⁿ-a.e. y ∈ G lies in M with θ(y) = k; hence Hⁿ(G ∖ M) = 0.
2. R.orients (via ae_restrict_iff'): Hⁿ-a.e. y ∈ M has an approximate tangent plane T; carrier_support_null: Hⁿ(M ∖ spt C) = 0.
3. Near such y, (M ∖ (M ∩ Q)) ∩ B_r(y) ⊆ M ∖ spt C and (Q ∖ (M ∩ Q)) ∩ B_r(y) ⊆ G ∖ M are null; approx_tangent_null_diff transfers T (from M) and Q (from Q, hasApproximateTangentSpaceAt_submodule) to M ∩ Q.
4. Uniqueness gives T = Q, and unfolding approxTangentPlane gives approxTangentPlane n M y = Q.

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
