# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1.smooth_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent-supplied proof of cbrcs_cutoff_extension, step 1 (Cutoff), isolated for an arbitrary open U and compact K ⊆ U.

1. (First neighbourhood.) ℝ^P = Euclid P is a finite-dimensional real normed space, hence locally compact and regular. Since K is compact, U is open and K ⊆ U, Mathlib's exists_open_between_and_isCompact_closure gives an open set V₁ with K ⊆ V₁, closure V₁ ⊆ U and closure V₁ compact.
2. (Second neighbourhood.) closure V₁ is a compact subset of the open set U, so the same lemma gives an open set V₂ with closure V₁ ⊆ V₂, closure V₂ ⊆ U and closure V₂ compact.
3. (Smooth Urysohn function.) closure V₁ is closed (isClosed_closure), V₂ is open and closure V₁ ⊆ V₂. Mathlib's exists_contDiff_support_eq_eq_one_iff (in the finite-dimensional real normed space ℝ^P, with smoothness order (⊤ : ℕ∞), i.e. C^∞, s := V₂, t := closure V₁) yields ζ : ℝ^P → ℝ with ContDiff ℝ ∞ ζ, range ζ ⊆ [0, 1], support ζ = V₂, and, for every x, x ∈ closure V₁ ↔ ζ(x) = 1.
4. (Topological support.) tsupport ζ = closure (support ζ) = closure V₂. By step 2 this set is compact, so ζ has compact support (HasCompactSupport ζ is exactly compactness of tsupport ζ), and tsupport ζ = closure V₂ ⊆ U.
5. (Values.) For every x, ζ(x) ∈ range ζ ⊆ [0, 1], so 0 ≤ ζ(x) and ζ(x) ≤ 1.
6. (The open set N.) Put N := V₁. N is open and K ⊆ N by step 1. If x ∈ N then x ∈ closure V₁ (subset_closure), so ζ(x) = 1 by the forward direction of the equivalence in step 3.
7. (Conclusion.) Steps 3–6 show that (ζ, N) has all required properties: ζ is C^∞ (step 3), has compact support and tsupport ζ ⊆ U (step 4), 0 ≤ ζ ≤ 1 (step 5), and N is open with K ⊆ N and ζ = 1 on N (step 6). ∎

Lean note (checked against the frozen imports, single theorem, no helper declarations): exists_open_between_and_isCompact_closure hK hU hKU, then exists_open_between_and_isCompact_closure hV₁compact hU hV₁U, then exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV₂open isClosed_closure hV₁V₂ (its order argument has type ℕ∞ in this Mathlib and its conclusion is ContDiff ℝ ↑⊤ ζ); rw [tsupport, hsupport] rewrites tsupport ζ to closure V₂.

## Key steps

1. Two applications of exists_open_between_and_isCompact_closure give open V₁ ⊇ K and V₂ ⊇ closure V₁ with closure V₂ compact and contained in U.
2. The smooth Urysohn lemma exists_contDiff_support_eq_eq_one_iff (order ∞, s := V₂, t := closure V₁) gives ζ with values in [0,1], support ζ = V₂ and ζ = 1 exactly on closure V₁.
3. tsupport ζ = closure V₂ is compact and contained in U; N := V₁ is open, contains K, and ζ = 1 on N.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical); cat snapshot project/lakefile.toml (no leanOptions)`
- `rg -n in snapshot mathlib/Mathlib and mathlib/lakefile.lean for 'theorem norm_iteratedFDeriv_smul_le|ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux|theorem exists_contDiff_support_eq_eq_one_iff|theorem exists_open_between_and_isCompact_closure|def precompR|def precompL|theorem norm_precompR_le|theorem norm_precompL_le|theorem norm_iteratedFDeriv_fderiv|theorem sum_choose_succ_mul|theorem Filter.EventuallyEq.extDeriv_eq|theorem support_iteratedFDeriv_subset|theorem HasCompactSupport.iteratedFDeriv|theorem iteratedFDeriv_zero|lemma Continuous.bounded_above_of_compact_support|theorem ContinuousLinearMap.fderiv_of_bilinear|theorem eventually_all_finset|theorem lintegral_mono_set|theorem setIntegral_congr_fun|maxSynthPendingDepth, .ofNat'; rg -n maxSynthPendingDepth in snapshot project (no match)`
- `lake env lean probes after import GMT.Ch07.Submission: #check norm_iteratedFDeriv_smul_le and ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (unknown identifiers: ContDiff.Bounds is outside the frozen import closure); #check exists_contDiff_support_eq_eq_one_iff, exists_open_between_and_isCompact_closure, ContinuousLinearMap.precompR/precompL/norm_precompR_le, ContinuousLinearMap.fderiv_of_bilinear, norm_iteratedFDeriv_fderiv, Finset.sum_choose_succ_mul, Filter.EventuallyEq.extDeriv_eq, Continuous.bounded_above_of_compact_support (all available); #synth Norm (E →L[ℝ] (D →L[ℝ] F) →L[ℝ] D →L[ℝ] G) fails; a verbatim copy of Mathlib's bilinear Leibniz aux proof fails by default and compiles with set_option maxSynthPendingDepth 3`
- `python3 -I scans of dag.json (1609 nodes): lean_statement/lean_name search for 'covectorEuclideanNorm (', 'IMRep (univ', 'testFormOnInclusion (subset_univ', 'TestFormOnConverges', 'iteratedFDeriv', 'Disjoint (tsupport' together with '.support', smooth-cutoff existentials '∃ ζ : Euclid P → ℝ … ContDiff … = 1', and names cbrcs_ce_*, rsd_mw_tfa_norm_props, rsd_cmr_support_subset_of_vanish (with statuses and candidate commits)`
- `grep -n in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py for _existing_lean_name_problem, _accepted_checkpoint, _dependency_problem, _machine_leaf, _leaf_author_task; leaf_verification.py check_source_delta forbidden-token regex; parent_verification.py check_parent_git_delta; swarm-project.json (leaf_lean_agent_review false, max_depth 6, max_children 12)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on all six child statements (pass); verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) replay (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `lake env lean /tmp/cbrcs-ce-q8w2/build/Challenges.lean (six statements elaborate in comparator challenge form); /tmp/cbrcs-ce-q8w2/Assembly.lean (hypothesis-only proof of the frozen parent type from the five used child types); /tmp/cbrcs-ce-q8w2/build/E2E.lean, which contains (a) the four new single-theorem child proofs, (b) the accepted proofs of the two reused declarations copied from candidate commits f492ba4a003c8f1324077e050d48667ae23c7100 and 02c6122c94d0280a6288d299659b2dab7b59e109, and (c) the proof of Submission.cbrcs_cutoff_extension; #print axioms reports propext, Classical.choice, Quot.sound only`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Nat/Choose/Sum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/lakefile.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c14d29cb77/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c14d29cb77/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cbrcs-ce-q8w2/build/Challenges.lean`
- `/tmp/cbrcs-ce-q8w2/Assembly.lean`
- `/tmp/cbrcs-ce-q8w2/build/E2E.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean. The project sets no Lean options, while Mathlib builds with maxSynthPendingDepth 3.

Mathlib.Analysis.Calculus.ContDiff.Bounds is not in the frozen import closure, so norm_iteratedFDeriv_smul_le, which step 4 of the supplied proof cites, is unavailable; the Leibniz estimate must be re-proved, which motivates the leibniz_bound child. Every other cited Mathlib lemma is available under the frozen imports (exists_open_between_and_isCompact_closure; exists_contDiff_support_eq_eq_one_iff, whose order argument is ℕ∞; Filter.EventuallyEq.extDeriv_eq; support_iteratedFDeriv_subset; precompR/precompL; fderiv_of_bilinear; norm_iteratedFDeriv_fderiv; Finset.sum_choose_succ_mul).

The DAG has accepted, byte-identical-type declarations rsd_mw_tfa_norm_props and rsd_cmr_support_subset_of_vanish, which are reused. It has no accepted iterated-derivative Leibniz bound, cutoff-multiplier continuity, IMRep lift to univ, or general compact smooth cutoff, so these are new children; the new names cbrcs_ce_* are free.

Leaves must be single theorems without set_option. All four new children satisfy this and pass the leaf token check.

Verification: all six statements validate and elaborate in comparator form. The hypothesis-only assembly and the sorry-free end-to-end file (children plus the parent proof) both compile with axioms propext, Classical.choice and Quot.sound only.
