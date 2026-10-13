# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.blowup_limit_cycle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (∂C = 0). Notation: for S ∈ 𝒟_{m+1}(V), (∂S)(ω) = S(dω) where dω = exteriorDerivativeTestOn V m ω has as underlying form the exterior derivative of ω (GeometricCurrentOn.boundary_apply); B_i := blowUp T x λ_i ∈ 𝒟_n(D_i), D_i := η_{x,λ_i}(U); currentEval(S, ω) = S(ω) if ω is a test form with tsupport ω inside the domain of S, and 0 otherwise.
1. If n = 0, BoundaryVanishes C is True by definition. Assume n = m + 1. Then BoundaryVanishes T says ∂T = 0, and we must show ∂C = 0. Currents are determined by their values (GeometricCurrentOn.ext), so it suffices to prove (∂C)(ω) = C(dω) = 0 for every ω ∈ 𝒟^m(ℝ^P).
2. Fix ω ∈ 𝒟^m(ℝ^P). Its topological support K := tsupport ω is compact (ω has compact support), hence bounded. By the sibling result blowup_domain_eventually (Submission.idtp_tpf_blowUp_domain_eventually, applied to U, x, (λ_i) and K), K ⊆ D_i for all sufficiently large i.
3. Fix such an i. The form ω is smooth with compact support and tsupport ω ⊆ D_i, so it defines ω_i ∈ 𝒟^m(D_i) with the same underlying form. Its exterior derivative dω_i = exteriorDerivativeTestOn D_i m ω_i has the same underlying form as dω (the ambient exterior derivative of ω), and tsupport dω ⊆ tsupport ω ⊆ D_i (exterior differentiation does not enlarge topological supports, tsupport_exteriorDerivative_subset). Hence, by the first branch of the definition of currentEval, currentEval(B_i, dω) = B_i(dω_i) = (∂B_i)(ω_i).
4. By dtc_blowUp_algebra (iv) (accepted: for λ > 0 and T ∈ 𝒟_{m+1}(U), ∂(blowUp T x λ) = blowUp (∂T) x λ) and ∂T = 0, we get ∂B_i = blowUp 0 x λ_i. The blow-up of the zero current is zero: by dtc_blowUp_algebra (i) with S = T = 0 and since 0 − 0 = 0 (evaluate on test forms), blowUp 0 x λ_i = blowUp 0 x λ_i − blowUp 0 x λ_i; evaluating at any η gives a = a − a for a := (blowUp 0 x λ_i)(η), so a = 0. (Equivalently, η_{x,λ_i#}0 evaluates the zero current on pulled-back forms.) Therefore currentEval(B_i, dω) = (blowUp 0 x λ_i)(ω_i) = 0 for all sufficiently large i.
5. The hypothesis ConvergesWeakly, applied to the test form dω ∈ 𝒟^{m+1}(ℝ^P), gives currentEval(B_i, dω) → C(dω). By step 4 this real sequence is eventually 0, so C(dω) = 0 by uniqueness of limits. Hence (∂C)(ω) = C(dω) = 0 for every ω ∈ 𝒟^m(ℝ^P), i.e. ∂C = 0, which is BoundaryVanishes C. ∎

## Key steps

1. Degree 0 is trivial; in degree m + 1 it suffices that C(dω) = 0 for every ω ∈ 𝒟^m(ℝ^P).
2. By blowup_domain_eventually, tsupport dω ⊆ tsupport ω lies in the domain of blowUp T x λ_i for large i, so currentEval(blowUp T x λ_i, dω) = ∂(blowUp T x λ_i)(ω).
3. dtc_blowUp_algebra (iv) and (i) give ∂(blowUp T x λ_i) = blowUp (∂T) x λ_i = blowUp 0 x λ_i = 0.
4. Weak convergence gives C(dω) = lim of an eventually zero sequence = 0, so ∂C = 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `python3 scan of dag.json lean_statements for IsConeCurrent | ConvergesWeakly[^→]*→[^∀]*BoundaryVanishes|BoundaryVanishes C | starProjection | ConvergesWeakly.*support | Orthonormal`
- `python3 scan of accepted dag.json lean_statements containing 'support' together with massOn|zeroRegion|VanishesOn|boundary`
- `dag.json lookup by lean_name: dtc_blowUp_algebra, dtc_vanish_off_support, dtc_blowUp_massOn_image, dimred_im_mass_measure, dimred_minimizing_monotonicity, density_and_tangent_cones, idtp_convergesWeakly_massOn_le, idtp_planar_cycle_eq_const_mul, dtc_blowUp_compactness, dimred_blowup_limit_moving_centres, dorag_ted_planes_limit, dorag_ted_pl_proj_limit_rank, cone_current_imrep_measure_smul_image, cone_current_apply_dilation_pullback, dor_ims_support_of_massOn_eq`
- `grep -n 'def GeometricCurrentOn.support|zeroRegion|VanishesOn|testFormOnInclusion' simongmt Chapter06/CurrentLocalEquality.lean; grep -n 'boundary_apply|exteriorDerivativeTestOn|GeometricCurrentOn.ext|zero_apply' Chapter06/Currents.lean; grep -n 'massOn|massAdmissibleOn|covectorEuclideanNorm' Chapter06/Mass.lean; grep -n 'Covector|DifferentialForm|IsTestForm' Chapter06/Forms.lean`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure, IsCompact.tendsto_subseq, Orthonormal.comp_linearIsometry, starProjection_eq_sum_rankOne, eq_starProjection_of_mem_of_inner_eq_zero, starProjection_orthogonal_val, norm_starProjection_apply_le, starProjection_apply_mem, orthonormal_iff_ite, finrank_span_eq_card, tendsto_pow_atTop_nhds_zero_of_lt_one, tendsto_one_div_add_atTop_nhds_zero_nat, StrictMono.id_le, squeeze_zero, 'class HasOrthogonalProjection'`
- `grep -rl idtp_tpf in dag.json, nodes/*/*.json and .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean (no match)`
- `grep -n 'Proof of 3.3(2)|h(spt|(13)' book/chapter-07.txt`
- `lake env lean /tmp/idtpf_check/Stmts.lean; lake env lean /tmp/idtpf_check/Assembly.lean; lake env lean /tmp/idtpf_check/Feas.lean; lake env lean /tmp/idtpf_check/Feas2.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca3ec8cf49/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/idtpf_check/Stmts.lean`
- `/tmp/idtpf_check/Assembly.lean`
- `/tmp/idtpf_check/Feas.lean`
- `/tmp/idtpf_check/Feas2.lean`

Pins and contract.
- The snapshot pins project b4d606db (equal to workspace HEAD) and mathlib 25730c7c; SimonGMT is 2b366308.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Existing lemmas.
- Not available as accepted lemmas: dilation invariance of cone supports, ∂C = 0 for blow-up limits, support exclusion for weak limits, compactness of n-planes in projection form.
- dtc_blowUp_compactness and dimred_blowup_limit_moving_centres conclude BoundaryVanishes C but are not accepted and carry heavy hypotheses.
- dorag_ted_pl_proj_limit_rank (accepted) only identifies limits of projections of basis vectors, so it is not reused.

Accepted lemmas used by the children:
- dtc_blowUp_algebra: (i) linearity, (iii) spt(blowUp T x λ) = dilation x λ '' spt T, (iv) ∂ commutes with blow-up.
- dtc_vanish_off_support.
- dimred_im_mass_measure (optional route in planar_support_eq).

Other cited results.
- idtp_planar_cycle_eq_const_mul is the parent's prerequisite (status decomposing).
- The parent glue uses density_and_tangent_cones and dimred_minimizing_monotonicity.
- SimonGMT: support = U ∖ zeroRegion with relatively compact open sets (CurrentLocalEquality.lean); boundary_apply ∂S(ω) = S(dω) with tsupport_exteriorDerivative_subset (Currents.lean); massOn = sSup over massAdmissibleOn (Mass.lean); IsTestForm = smooth ∧ compact support (Forms.lean).
- Mathlib: the μHE Haar-measure instance and isometry invariance, plus all cited projection/orthonormal/compactness lemmas, exist under the cited names. HasOrthogonalProjection is a Prop class.

Book. chapter-07.txt lines 512–530 contain the proof of 3.3(2) and the flatness h(spt S, L, ρ, x) via q onto L^⊥; (13) is at line 581.

Names. idtp_tpf_* occurs nowhere in dag.json, in the node JSONs or in the ch07 worktrees.

Lean.
- All 7 child statements elaborate.
- The parent's frozen type is proved from the child stubs; axioms are propext, Classical.choice, Quot.sound and sorryAx from the stubs only.
- All 7 children are proved in Lean against stubs of the cited accepted lemmas only. plane_subsequence_limit and blowup_domain_eventually are fully proved with standard axioms.
