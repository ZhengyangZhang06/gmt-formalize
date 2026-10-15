# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.gauss_green_complement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 5, i.e. printed (11) 'Repeating the same argument with U ∖ E in place of E', which is identity (GG) for ℝ^P ∖ F with normal −ν. Dependency: divergence_integral_zero (Submission.codim1_rdo_dg_vdl_integral_divergence_eq_zero).
1. Fix φ : ℝ^P → ℝ^P, C¹ with compact support and tsupport φ ⊆ D, and let f(z) := trace(Dφ(z)).
2. f is integrable. Dφ is continuous because φ is C¹. A ↦ trace A is a linear map on the finite-dimensional space of linear maps ℝ^P → ℝ^P, hence continuous, so f is continuous. Dφ has compact support (HasCompactSupport.fderiv) and trace 0 = 0, so f has compact support. A continuous compactly supported function is integrable.
3. Since F is measurable and f is integrable, ∫_F f + ∫_{F^c} f = ∫ f (integral_add_compl), and ∫ f = 0 by divergence_integral_zero. With the hypothesis ∫_F f = −∫⟨φ, ν⟩ dμ, this gives ∫_{F^c} f = ∫⟨φ, ν⟩ dμ.
4. Pointwise ⟨φ(z), −ν(z)⟩ = −⟨φ(z), ν(z)⟩, and ∫(−g) dμ = −∫ g dμ for every g (integral_neg; no integrability needed). Hence −∫⟨φ, −ν⟩ dμ = ∫⟨φ, ν⟩ dμ = ∫_{F^c} f. ∎
Validation note (not part of the proof): a Lean proof of exactly this frozen statement from divergence_integral_zero compiled against the frozen import closure (scratch file /tmp/vdl-split-check/F/Proof.lean, outside the repository).

## Key steps

1. z ↦ trace Dφ(z) is continuous with compact support, hence integrable.
2. ∫_F + ∫_{F^c} = ∫ = 0 by divergence_integral_zero.
3. Therefore ∫_{F^c} trace Dφ = ∫⟨φ, ν⟩ dμ = −∫⟨φ, −ν⟩ dμ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git status / git log in the workspace (clean, HEAD b4d606db = snapshot project commit)`
- `python3 scans of dag.json: frozen types of de_giorgi-a1 children (cutoff_estimates-a1, sobolev_perimeter-a1, selected volume_density_lower-a1); regex scan for trace/fderiv/cutoff/bump/rpow statements; collision check of the 7 proposed codim1_rdo_dg_vdl_* names and 5 scratch helper names (0 hits among 974 nodes)`
- `git show bc0bc2b9 -- GMT/Ch07/Submission.lean (accepted Submission.dorag_th_radial_cutoff technique and type)`
- `rg in snapshot mathlib: integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable, integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable, tendsto_integral_filter_of_dominated_convergence, integral_add_compl, trace_eq_sum_inner, geom_mean_le_arith_mean_weighted, norm_fderiv_le_of_lipschitz, HasCompactSupport.fderiv, hasDerivAt_iff_tendsto_slope_zero, contDiff_one_iff_deriv, Continuous.integral_hasStrictDerivAt`
- `lake env lean -DautoImplicit=false /tmp/vdl-split-check/Avail.lean (#check of the above inside the frozen import closure of GMT.Ch07.Submission)`
- `sed -n 640,760p book/chapter-03.txt (Simon Ch. 3, 4.3, (10)-(11))`
- `sed of runtime.py (_decompose, _solve_children, _existing_lean_name_problem), prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK), verifier/gmt-compare.py header; cat swarm-project.json (max_depth 6, max_children 12)`
- `lake env lean -DautoImplicit=false on /tmp/vdl-split-check/Assembly.lean, /tmp/vdl-split-check/EndToEnd.lean and /tmp/vdl-split-check/{A,B,C,D,E,F,G}/Proof.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-0c71c3da25/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/vdl-split-check/Assembly.lean`
- `/tmp/vdl-split-check/EndToEnd.lean`
- `/tmp/vdl-split-check/A/Proof.lean`
- `/tmp/vdl-split-check/B/Proof.lean`
- `/tmp/vdl-split-check/C/Proof.lean`
- `/tmp/vdl-split-check/D/Proof.lean`
- `/tmp/vdl-split-check/E/Proof.lean`
- `/tmp/vdl-split-check/F/Proof.lean`
- `/tmp/vdl-split-check/G/Proof.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) matches the clean workspace HEAD. Library: Mathlib's integration-by-parts lemmas exist in the snapshot (IntegrationByParts.lean:179-226) but are NOT in the frozen import closure of GMT.Ch07.Submission (Lean reports Unknown identifier). divergence_integral_zero therefore uses integral_add_right_eq_self, tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67) and LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25). All of the following are available: AM-GM (MeanInequalities.lean:129), integral_add_compl (Bochner/Set.lean:158), norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947), HasCompactSupport.fderiv (FDeriv/Const.lean:389), hasDerivAt_iff_tendsto_slope_zero (Deriv/Slope.lean:82), contDiff_one_iff_deriv (ContDiff/Deriv.lean:98), Continuous.integral_hasStrictDerivAt (FundThmCalculus.lean:656) and Real.smoothTransition. No local or accepted DAG declaration states any of the following: the thin-annulus C1 cut-off with O(1/delta) gradient, the discrete integration lemma, the finite-difference inequality, int div phi = 0, or the complement Gauss-Green identity. The accepted dorag_th_radial_cutoff (commit bc0bc2b9) has a fixed r/2-to-r ratio, and doragm_sab_cutoff_profile has no gradient bound, so no identical-type reuse is possible. DAG: the 7 proposed codim1_rdo_dg_vdl_* names and the 5 scratch helper names occur in none of the 974 nodes. Lean: all 7 child types elaborate in the contract scope. Assembly.lean proves the parent's exact frozen type from the 7 children plus stubs of the 2 resolved sibling dependencies. EndToEnd.lean compiles real proofs of all 7 children (#print axioms: propext, Classical.choice, Quot.sound for each) together with the assembly (parent axioms: propext, sorryAx, Classical.choice, Quot.sound, where sorryAx comes only from the two sibling stubs). Runtime: depth 5 < max_depth 6, so the children are leaves. The child comparator elaborates the frozen type in the contract scope and checks it with exact Submission.<lean_name>.
