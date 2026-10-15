# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1.cutoff_homotopy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the selected parent proof: the cutoff ψ := ζ·K₀γ, its smoothness and compact support, locality of d, and the homotopy formula. Here it is isolated as a statement about K₁(dγ) alone.

1. Homotopy formula for γ. γ is a test form, so it is C^∞ (first component of its membership in TestFormOn univ (q+1)). Applying (H) with β := γ: K₀γ is C^∞, and d(K₀γ)(x) + K₁(dγ)(x) = γ(x) for every x ∈ ℝ^P.

2. Cutoff. Let ζ be the ContDiffBump centred at 0 with rIn = |ρ| + 1 and rOut = |ρ| + 2, so 0 < rIn < rOut. Then:
 - ζ is C^∞ and has compact support;
 - for every x ∈ ball(0, rIn), ζ = 1 on a neighbourhood of x (ContDiffBump.eventuallyEq_one_of_mem_ball).
 The radius |ρ| + 1 is positive even when ρ ≤ 0; in that case the conclusion is vacuous.

3. The primitive ψ. Put ψ(y) := ζ(y)·K₀γ(y).
 - ψ is C^∞, by ContDiff.smul of ζ and the C^∞ form K₀γ from step 1.
 - ψ has compact support, since ζ does (HasCompactSupport.smul_right).
 - tsupport ψ ⊆ ℝ^P.
 So ψ ∈ TestFormOn univ q.

4. Locality. Let ‖x‖ < ρ. Then ‖x‖ < |ρ| + 1 = rIn, i.e. x ∈ ball(0, rIn). By step 2, ζ = 1 on a neighbourhood of x. There ψ = 1·K₀γ = K₀γ, i.e. ψ =ᶠ[𝓝 x] K₀γ. The exterior derivative at x is built from the Fréchet derivative at x, so it depends only on the germ of the form at x (Filter.EventuallyEq.extDeriv_eq). Hence dψ(x) = d(K₀γ)(x).

5. Conclusion. By step 1, K₁(dγ)(x) = γ(x) − d(K₀γ)(x). By step 4 this equals γ(x) − dψ(x). ∎

(A Lean proof following exactly these steps compiled during decomposition against the frozen contract. It depends only on propext, Classical.choice and Quot.sound.)

## Key steps

1. (H) with β := γ (a C^∞ test form): K₀γ is C^∞ and d(K₀γ) + K₁(dγ) = γ everywhere.
2. ψ := ζ·K₀γ is a test q-form, where ζ is a bump equal to 1 near every point of ball(0, |ρ|+1).
3. For ‖x‖ < ρ, ψ = K₀γ near x, so dψ(x) = d(K₀γ)(x) (Filter.EventuallyEq.extDeriv_eq), whence K₁(dγ)(x) = γ(x) − dψ(x).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git status/log of the workspace (branch problems/ch07 at b4d606d, clean)`
- `python3 -I over dag.json: the selected node (depth 5, decomposing, depends on radial_homotopy-a1); its siblings radial_homotopy (decomposing, then speculative-lean), compact_im_param, cone_param and param_series_im; dependency classes (1286 sibling, 896 non-sibling, every non-sibling target accepted)`
- `python3 -I over the 2202 accepted lean_statements for: TestFormOnConverges | Disjoint (tsupport | .support ⊆ | IMRep with |T ω| ≤ | R.measure univ | IsUnitOrientationOf | curryLeft | ContDiffBump`
- `git show 493589396f:GMT/Ch07/Submission.lean, 02c6122c94:GMT/Ch07/Submission.lean and 8d68dfd93a:GMT/Ch07/Submission.lean (accepted proofs of cmcs_rc_order_zero_current, rsd_cmr_support_subset_of_vanish and dpf_pfc_testFormOnConverges_zero_uniform; none adds an import)`
- `grep -n in the Mathlib snapshot: Analysis/Normed/Module/Alternating/Curry.lean (curryLeft_add, curryLeft_smul, curryLeft_zero, norm_curryLeft, curryLeftLI); Analysis/Calculus/BumpFunction/Basic.lean (one_of_mem_closedBall, zero_of_le_dist, eventuallyEq_one_of_mem_ball, hasCompactSupport, contDiff); Analysis/Calculus/DifferentialForm/Basic.lean (Filter.EventuallyEq.extDeriv_eq)`
- `sed simongmt Chapter06/{Currents,Forms,Mass,CurrentLocalEquality}.lean for TestFormOnConverges, GeometricCurrentOn.continuous', exteriorDerivativeTestOn, boundary_apply, GeometricCurrentOn.ext, zeroRegion, support, IsSmoothForm`
- `python3 -I, loading verifier/gmt-compare.py via importlib: contract_scope(GMT/Ch07/Contract.lean, GMT.Ch07.main_theorem) gives the 7 replayed scope commands`
- `lake env lean /tmp/cc-decomp/{Smoke,Debug1,Assembly,Assembly2,ChildA,ChildB,ChildC}.lean and /tmp/cc-decomp/final/{Final,Final2}.lean, with #print axioms`
- `python3 -I scan of nodes/*/{decomposition-v*,decomposition-scope-v*,parent-child-handoff}.json (5951 files) and dag.json for dimred_cs_sos_cfs_cc_ (no match)`
- `sed -n 420,560p book/chapter-06.txt (Simon 6.2.25–2.32: homotopy formula, affine homotopy, the cone 0 ⨯ T, ∂(0 ⨯ T) = T − 0 ⨯ ∂T)`
- `Independent reviewer agent: re-ran Final.lean and Final2.lean, the comparator-scope challenge files and validate_lean_statement (/tmp/cc-review); verdict ACCEPT on both rounds`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-77a7f533dd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-77a7f533dd/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-restrict-curren-7244aadae8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-456fc8281b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cc-decomp/final/Final2.lean`
- `/tmp/cc-decomp/final/Final.lean`
- `/tmp/cc-decomp/Assembly2.lean`
- `/tmp/cc-decomp/ChildA.lean`
- `/tmp/cc-decomp/ChildB.lean`
- `/tmp/cc-decomp/ChildC.lean`

Pins. The manifest records project b4d606db and Mathlib 25730c7c. The workspace is at b4d606d and its working tree is clean.

Library gaps. Neither Mathlib nor SimonGMT has the cone current, a C⁰ bound for IMRep-represented currents, or a cut-off radial operator, so three new lemmas are needed. The pinned Mathlib supplies every API they use:
- curryLeft_add, curryLeft_smul, norm_curryLeft, curryLeftLI;
- ContDiffBump.{one_of_mem_closedBall, zero_of_le_dist, eventuallyEq_one_of_mem_ball, hasCompactSupport, contDiff};
- Filter.EventuallyEq.extDeriv_eq;
- intervalIntegral.norm_integral_le_of_norm_le_const, norm_integral_le_of_norm_le;
- integrable_toReal_of_lintegral_ne_top, integral_toReal.

Reuse. Two accepted DAG declarations are reused with byte-identical frozen types: cmcs_rc_order_zero_current (commit 4935893) and rsd_cmr_support_subset_of_vanish (commit 02c6122). Neither commit adds an import. Considered but not used:
- dpf_pfc_testFormOnConverges_zero_uniform (used in an earlier compiled variant);
- dtc_bc_lc_fd_lz_action_bound (it bounds with covectorEuclideanNorm, not the operator norm);
- unit_orientation_norm_le_one and regcomp_rim_action_integrable (not needed for the direct proof).

Uncle dependency. radial_homotopy is not accepted, and every non-sibling dependency in dag.json points to an accepted node. So the children take radial_homotopy's conclusions as hypotheses, and the selected node discharges them.

Lean checks. Final2.lean replays the comparator scope from gmt-compare.py and proves all five children; each depends only on propext, Classical.choice and Quot.sound. It also proves the frozen parent type from the children plus a stub for the uncle; the only extra axiom, sorryAx, comes from that stub.

Names. The three new names occur nowhere in dag.json or in the 5951 decomposition, scope and handoff files.

Source. Simon Ch. 6, 2.25–2.32 (chapter-06.txt lines 441–551) is the source of the cone 0 ⨯ T and of ∂(0 ⨯ T) = T − 0 ⨯ ∂T.
