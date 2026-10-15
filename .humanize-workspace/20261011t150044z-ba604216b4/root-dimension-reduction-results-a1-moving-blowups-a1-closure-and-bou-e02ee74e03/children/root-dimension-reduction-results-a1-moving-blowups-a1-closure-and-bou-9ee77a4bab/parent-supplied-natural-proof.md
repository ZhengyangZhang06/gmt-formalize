# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.pairing_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4 and 6 of the parent proof (Γ_k(ω) − C(ω) = [Γ_k(ω) − ∫τ₀(ω)dν_{φ(k)}] + [∫τ₀(ω)dν_{φ(k)} − ∫τ₀(ω)dν] → 0), for one form w. The only sibling used is pairing_error (Submission.dmcbr_ci_bl_pairing_error_le). Notation: B̄_R := closedBall 0 R and δ_k(R) := ∫⁻_{B̄_R} ‖τ_k − ζ₀‖ₑ dν_k.
1. (Bounds for w.) Since w is continuous with compact support, there is A ∈ ℝ with ‖w(x)‖ ≤ A for all x (Continuous.bounded_above_of_compact_support). The set tsupport w is compact, hence bounded, so tsupport w ⊆ B̄_{R₀} for some R₀ ∈ ℝ (Bornology.IsBounded.subset_closedBall). Put R := max(R₀, 1). Then R > 0, tsupport w ⊆ B̄_R (closedBall_subset_closedBall), and w(x) = 0 for every x ∉ B̄_R (image_eq_zero_of_notMem_tsupport).
2. (Main term.) f(x) := ζ₀(w(x)) is continuous, since ζ₀ is a continuous linear map. It has compact support by HasCompactSupport.comp_left with ζ₀(0) = 0. Each ν_k is finite on compact sets, i.e. IsFiniteMeasureOnCompacts ν_k (build the instance from the hypothesis). Hence f is ν_k-integrable for every k (Continuous.integrable_of_hasCompactSupport).
3. (The error bound tends to 0.) Let e_k := ofReal(A)·δ_k(R). Since δ_k(R) → 0 (hypothesis, as R > 0) and ofReal(A) ≠ ∞, e_k → ofReal(A)·0 = 0 (ENNReal.Tendsto.const_mul, mul_zero). Hence eventually e_k < 1 (tendsto_order), and then e_k ≠ ∞ (ne_top_of_lt). Moreover e_k.toReal → 0, by composing ENNReal.tendsto_toReal at 0 with e_k → 0 and using ENNReal.toReal_zero.
4. (Error term.) Fix k with e_k < 1. Apply the sibling pairing_error (Submission.dmcbr_ci_bl_pairing_error_le) with ν' := ν_k, τ := τ_k, ζ₀, w, A and R. Its hypotheses hold by the a.e. strong measurability of τ_k, the continuity of w, step 1, step 2 and e_k ≠ ∞. It gives |∫ τ_k(x)(w(x)) dν_k − ∫ f dν_k| ≤ e_k.toReal. This holds for all sufficiently large k and e_k.toReal → 0, so d_k := ∫ τ_k(x)(w(x)) dν_k − ∫ f dν_k tends to 0 (squeeze_zero_norm', using ‖d_k‖ = |d_k|).
5. (Conclusion.) By the C_c-convergence hypothesis applied to f (step 2), ∫ f dν_k → ∫ f dν. Since d_k + ∫ f dν_k = ∫ τ_k(x)(w(x)) dν_k for every k, Tendsto.add, zero_add and Tendsto.congr give ∫ τ_k(x)(w(x)) dν_k → 0 + ∫ f dν = ∫ ζ₀(w(x)) dν(x). ∎

## Key steps

1. Choose A with ‖w‖ ≤ A, and R = max(R₀,1) > 0 with tsupport w ⊆ B̄_R(0), so w = 0 off B̄_R(0).
2. f = ζ₀∘w is continuous with compact support, hence ν_k-integrable for every k.
3. e_k = ofReal(A)·δ_k(R) → 0, so eventually e_k < 1 (finite), and e_k.toReal → 0.
4. pairing_error gives |∫τ_k(w)dν_k − ∫f dν_k| ≤ e_k.toReal eventually, so this difference tends to 0.
5. ∫f dν_k → ∫f dν by hypothesis; adding the two limits gives the claim.

## Reference use

### local-project

Queries:
- `cat SNAP/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git log -1 (workspace HEAD b4d606db1); cmp SNAP/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 -I scans of RUN/dag.json (2102 nodes): dmcbr_ci_blowup_limit vs cbr_ci_blowup_limit (identical lean_statement and natural_proof; statements differ only in sibling names); twin subtree statuses (blowup_measure accepted ef60a96f, covector_norm rlcr-lean, blowup_scale/density_bounds/rescaled_bounds/constant_limit/mass_bound/pairing_tendsto speculative-ready, other depth-6 leaves decomposing); frozen types of dmcbr_ci_dilation_calculus, dmcbr_ci_dilation_slice_property (identical to the accepted cbr_ci_* twins), cbr_ci_const_vector_massOn (accepted bc226ec6), cmcs_restrict_current (accepted a7cb2361), cbr_ci_bl_blowUp_restrict_scaling; lean_name lookup of the ten proposed dmcbr_ci_bl_* names -> none present`
- `read NODES/<twin>/decomposition-v1.json and decomposition-audit-v1.json for d8eab44069 (blowup_limit), 2a563f59dd (density_bounds), 6264bc6f37 (rescaled_bounds), 5981b082bc (constant_limit): all acceptable, every node natural_proof_acceptable; atomic decisions 9d402d3e08 (covector_norm, ~60-line scratch proof) and 6da3570ebf (blowup_scale, ~90-line scratch proof)`
- `git show 89c100ef / c23d5415 / a0358e1b / 84ebb489 / 80516330 / e4102347 / 7ebe5255 (twin speculative drafts); git show ef60a96f:, a7cb2361:, bc226ec6:GMT/Ch07/Submission.lean -> accepted declarations cbr_ci_bl_blowUp_restrict_scaling, cmcs_restrict_current, cbr_ci_const_vector_massOn with types identical to dag.json`
- `sed /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: node.depth >= max_depth stops splitting; _existing_lean_name_problem: only accepted identical-type names are shareable; _leaf_author_task: a child adds only its single theorem, no helper declarations; child proof_base_commit = parent dispatch commit) and swarm-project.json (max_depth 6, max_children 12)`
- `rg -c dmcbr_ci_bl SNAP/project (no match, exit 1); rg -l dmcbr_ci_bl GMT .lake/packages/simongmt (no match, exit 1); rg -c 'cbr_ci_bl_blowUp_restrict_scaling|cmcs_restrict_current' SNAP/project (no match: DAG-accepted, not in the frozen base)`
- `rg -n in SNAP/mathlib/Mathlib: integral_withDensity_eq_integral_toReal_smul (MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:318, root namespace), ENNReal.limsup_const_mul_of_ne_top (Order/Filter/ENNReal.lean:165), tendsto_measure_cthickening_of_isClosed (MeasureTheory/Constructions/BorelSpace/Metric.lean:143), enorm_integral_le_lintegral_enorm (MeasureTheory/Integral/Bochner/Basic.lean:333), ContinuousAlternatingMap.opNorm_le_bound (Analysis/Normed/Module/Alternating/Basic.lean:241)`
- `lake env lean Names.lean: #check of 165 library names cited by the child proofs -> all resolve (integral_withDensity_eq_integral_toReal_smul is root-level, measure_ball_pos is Metric.measure_ball_pos); deprecated ContinuousLinearMap.smul_apply (use smul_apply) and ofReal_norm_eq_enorm (use ofReal_norm)`
- `lake env lean Remarks.lean: ContinuousAlternatingMap.map_perm unknown (AlternatingMap.map_perm on toAlternatingMap exists); Finset.prod_le_prod needs MulLeftMono; push_neg deprecated (push Not); ofReal_norm d : ofReal ‖d‖ = ‖d‖ₑ for d : MultiVector P n; dilation a lam y = blowUpMap a lam y by simp [dilation, dilationCLM, blowUpMap, smul_sub]; abel`
- `lake env lean Types.lean (the 12 child types as theorems after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens: sorry warnings only)`
- `lake env lean Assembly.lean (exact frozen parent type proved from the 12 child types and the 3 sibling types as axioms, no sorry; #print axioms: propext, Classical.choice, Quot.sound plus 14 of the 15 stubs, pairing_error entering only through pairing_tendsto and mass_bound)`
- `python3 -I: _recursive_lean.lean_contract.validate_lean_statement on all 12 child types -> valid and unchanged`
- `sed SimonGMT Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn = sSup ofReal T ω), Chapter06/Currents.lean (TestFormOn, GeometricCurrentOn, WeaklyConvergesOn, boundary, WeaklyConvergesOn.boundary), Chapter06/Forms.lean (Covector, IsTestForm)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-e02ee74e03/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-e02ee74e03/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/speculative-process-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2a563f59dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2a563f59dd/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6264bc6f37/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6264bc6f37/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5981b082bc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5981b082bc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-9d402d3e08/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6da3570ebf/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/speculative-prompt-v1.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/tmp/dmcbr_bl_decomp/Types.lean`
- `/tmp/dmcbr_bl_decomp/Assembly.lean`
- `/tmp/dmcbr_bl_decomp/Names.lean`
- `/tmp/dmcbr_bl_decomp/Remarks.lean`

The snapshot is compatible: its pins match and its contract is byte-identical to Submission.lean. The snapshot and SimonGMT contain no blow-up-limit declaration and no dmcbr_ci_bl name. The selected node has the same frozen type and supplied proof as the twin cbr_ci_blowup_limit, whose split and sub-splits were all audited acceptable. Because this node sits at depth 5 of 6, the twin's audited leaf statements are lifted to give 12 children with identical types. Two of them reuse the accepted cbr_ci_bl_blowUp_restrict_scaling and cmcs_restrict_current; the other ten have fresh dmcbr_ci_bl_* names. Every library name the child proofs cite resolves at the pinned revisions under the non-deprecated name given. All 12 child types elaborate and pass the validator. A sorry-free assembly proves the exact parent type from them and the three sibling types, using only propext, Classical.choice and Quot.sound beyond the stubs.
