# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1.mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 7 of the supplied proof of the selected node (the mass bound (H4)), Simon 7.5.3 and 7.5.5 (chapter-07.txt lines 790–901). Departure: step 6 of the supplied proof (ball(0, R) ⊆ η_i(U) for large i) is replaced by a case distinction on the support of ω. So neither openness of U nor x ∈ U is needed. Sibling used: testform_corr (Submission.dtc_blowUp_testForm_corr), parts (a) and (c).

Notation. η_i := η_{x_i,λ_i} = dilation x_i λ_i, so η_i(z) = −λ_i⁻¹x_i + λ_i⁻¹z = λ_i⁻¹(z − x_i). S_i := blowUp T x_i λ_i ∈ 𝒟_n(η_i(U)). For an ambient n-form ω, currentEval(S_i)(ω) = S_i(⟨ω, h⟩) if h : (ω is C^∞ with compact support) ∧ tsupport ω ⊆ η_i(U) holds, and 0 otherwise (Contract definition). |α| := covectorEuclideanNorm α.

1. (Constants.) Take C and r₀ > 0 from the hypothesis and fix R > 0. Put c := max(C, 0)·R^n. Then c ≥ 0.
2. (Large indices.) Since x_i → x, x_i ∈ ball(x, r₀) for all large i. Since λ_iR → 0·R = 0 < r₀, λ_iR < r₀ for all large i. Fix i with both properties and an n-form ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ ball(0, R) and |ω(y)| ≤ 1 for all y. As λ_i > 0 and R > 0, 0 < λ_iR < r₀.
3. (Case tsupport ω ⊄ η_i(U).) The condition in the definition of currentEval fails, so currentEval(S_i)(ω) = 0 ≤ c.
4. (Case tsupport ω ⊆ η_i(U).) Then ω is a test form in η_i(U); write ω̃ ∈ 𝒟^n(η_i(U)) for it (same underlying form). By definition currentEval(S_i)(ω) = S_i(ω̃). By testform_corr (a) (with P, n, U, x := x_i, λ := λ_i > 0) there is ω' ∈ 𝒟^n(U) with ω'(z) = ω(η_i(z)) for all z ∈ ℝ^P. By testform_corr (c) (with T, ω̃, ω'), S_i(ω̃) = (λ_i⁻¹)^n·T(ω').
5. (Support of ω'.) As functions ω' = ω∘η_i. The affine map η_i is continuous, so tsupport(ω∘η_i) ⊆ η_i⁻¹(tsupport ω) (tsupport_comp_subset_preimage) ⊆ η_i⁻¹(ball(0, R)). For z ∈ ℝ^P, |η_i(z)| = λ_i⁻¹|z − x_i|, so η_i(z) ∈ ball(0, R) iff |z − x_i| < λ_iR. Hence tsupport ω' ⊆ ball(x_i, λ_iR).
6. (Admissibility and the mass hypothesis.) For every z, |ω'(z)| = |ω(η_i(z))| ≤ 1. With step 5, ω' ∈ massAdmissibleOn U n (ball(x_i, λ_iR)). GeometricCurrentOn.le_massOn gives ofReal(T(ω')) ≤ T.massOn(ball(x_i, λ_iR)). The hypothesis with y := x_i ∈ ball(x, r₀) and ρ := λ_iR ∈ (0, r₀) gives T.massOn(ball(x_i, λ_iR)) ≤ ofReal(C(λ_iR)^n). Hence ofReal(T(ω')) ≤ ofReal(C(λ_iR)^n).
7. (Real bound.) By ENNReal.ofReal_le_ofReal_iff', T(ω') ≤ C(λ_iR)^n or T(ω') ≤ 0. Since (λ_iR)^n ≥ 0, both C(λ_iR)^n and 0 are ≤ max(C, 0)(λ_iR)^n. So T(ω') ≤ max(C, 0)·(λ_iR)^n.
8. (Conclusion.) Since (λ_i⁻¹)^n > 0 and (λ_i⁻¹)^n(λ_iR)^n = (λ_i⁻¹λ_iR)^n = R^n,
 currentEval(S_i)(ω) = (λ_i⁻¹)^n·T(ω') ≤ (λ_i⁻¹)^n·max(C, 0)·(λ_iR)^n = max(C, 0)·R^n = c.
Steps 3 and 8 give currentEval(S_i)(ω) ≤ c for all large i and all such ω, with c independent of i and ω. ∎

Formalization notes (this exact frozen type was proved in a scratch build, with testform_corr as the only non-standard axiom). Eventuality comes from hxs (ball_mem_nhds x hr₀) and gt_mem_nhds applied to Tendsto (λ_i·R) (from hlam.mul_const R, simpa). Then use unfold currentEval; split_ifs. The identity dilation x_i λ_i z = λ_i⁻¹ • (z − x_i) follows from simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_sub]; abel. For the support use tsupport_comp_subset_preimage with continuity continuous_const.add (dilationCLM P λ_i).continuous. Finish with mem_ball_zero_iff, norm_smul, inv_mul_lt_iff₀, GeometricCurrentOn.le_massOn, ENNReal.ofReal_le_ofReal_iff', mul_pow and inv_mul_cancel_left₀.

## Key steps

1. c := max(C, 0)·R^n ≥ 0; for large i, x_i ∈ ball(x, r₀) and λ_iR < r₀.
2. If tsupport ω ⊄ η_i(U), currentEval(S_i)(ω) = 0 ≤ c.
3. Otherwise testform_corr gives ω' = ω∘η_i ∈ 𝒟^n(U) with S_i(ω) = λ_i^{−n}T(ω'). ω' is admissible for M_{ball(x_i, λ_iR)}(T): tsupport ω' ⊆ ball(x_i, λ_iR) and |ω'| ≤ 1.
4. The mass hypothesis gives T(ω') ≤ max(C, 0)(λ_iR)^n, hence currentEval(S_i)(ω) ≤ max(C, 0)R^n.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n '"simongmt"' -A8 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 scans of dag.json: status, lean_name and depends_on of the zero_scale_limit_plane children and of testform_correspondence-a1; lean_statement lookup of codim1_zsl_blowUp_isBoundaryOfRegion, codim1_zsl_graph_area_formula, codim1_zsl_flat_graph_limit, dtc_blowUp_testForm_corr and codim1_zsl_graph_blowup_limit (byte equality with the handoff); scan of lean statements containing 'blowUp' together with 'massOn' or 'covectorEuclideanNorm'`
- `python3 dump of the parent's decomposition-v2.json (subproblem statements and Lean types) and comparison of its testform_corr entry with the accepted node's parent-child-handoff.json (natural proof and key steps byte-equal)`
- `grep -n 'def check_source_delta' -A40 leaf_verification.py; grep -n '_existing_lean_name_problem|_solve_children|_install_parent_supplied_child_handoff|prerequisite_ids' runtime.py`
- `grep -n 'def IsTestForm|abbrev exteriorDerivative|theorem exteriorDerivative_apply|def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.le_massOn|def testFormOnSubmodule|structure GeometricCurrentOn|theorem tsupport_exteriorDerivative_subset' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass}.lean; sed -n 1,330p GMT/Ch07/Contract.lean (currentEval, ConvergesWeakly, dilation, blowUp, IsBoundaryOfRegion)`
- `grep -rn 'ContinuousOn.measurable_piecewise|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|setIntegral_congr_fun|IsCompact.tendsto_subseq|norm_image_sub_le_of_norm_fderiv_le|ContDiffOn.continuousOn_fderiv_of_isOpen' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/gbl-split/Names.lean (#check of about 50 cited Mathlib/SimonGMT lemmas)`
- `lake env lean /tmp/gbl-split/FinalTypes.lean; lake env lean /tmp/gbl-split/FinalAssembly.lean (#print axioms Submission.codim1_zsl_graph_blowup_limit)`
- `lake env lean /tmp/gbl-split/proofs/{A,B,C,D}_work.lean with #print axioms (scratch proofs of the four new children)`
- `for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl_gbl $r -- 'GMT/*.lean' (positive control dtc_blowUp_testForm_corr); grep -c of each new name in dag.json, .lake/packages/simongmt, .lake/packages/mathlib/Mathlib, GMT/`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0d752561a6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-testform-correspondence-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/gbl-split/Names.lean`
- `/tmp/gbl-split/FinalTypes.lean`
- `/tmp/gbl-split/FinalAssembly.lean`
- `/tmp/gbl-split/proofs/A_work.lean`
- `/tmp/gbl-split/proofs/B_work.lean`
- `/tmp/gbl-split/proofs/C_work.lean`
- `/tmp/gbl-split/proofs/D_work.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG.
- The selected node is 'decomposing' at depth 4, and its frozen type in dag.json equals the handoff's.
- Its dependencies blowup_region, graph_area and flat_limit are 'decomposing' under another parent. They therefore cannot be reused as children here; graph_representation takes the first two as hypotheses.
- dtc_blowUp_testForm_corr is accepted (candidate 5e184fbc), with type and statement byte-equal to the reused entry.
- No accepted node already states the needed blow-up mass bound for moving centres. The nearest are dtc_blowUp_massOn_image (fixed W, accepted) and dtc_bc_bh_blowUp_massOn_ball_bounded (fixed centre, unaccepted).
Library.
- The SimonGMT and Contract definitions match the children's proofs: IsTestForm = C^∞ ∧ compact support, TestFormOn = IsTestForm ∧ tsupport ⊆ U, exteriorDerivative = extDeriv, tsupport_exteriorDerivative_subset, massAdmissibleOn, le_massOn, covectorEuclideanNorm, and currentEval as a dite on IsTestForm ∧ tsupport ⊆ domain.
- Every cited Mathlib lemma exists in the snapshot, e.g. ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean:523), setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), setIntegral_congr_fun (Bochner/Set.lean:73), IsCompact.tendsto_subseq (Topology/Sequences.lean:298), Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499) and ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916). Measurable.measurableSet_preimage does not exist and is not cited.
Lean.
- All 5 child types elaborate.
- With the children and the 3 unaccepted dependencies as axioms, the selected type is proved, using only standard axioms besides those declarations.
- Scratch proofs of all 4 new children compile against their exact types without sorry.
- New names have 0 occurrences anywhere checked; the positive control was found.
