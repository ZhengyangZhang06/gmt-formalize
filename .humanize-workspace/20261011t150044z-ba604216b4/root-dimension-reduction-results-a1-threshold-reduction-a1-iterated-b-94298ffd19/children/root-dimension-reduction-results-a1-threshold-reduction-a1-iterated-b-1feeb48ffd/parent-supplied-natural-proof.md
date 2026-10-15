# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1.diagonal_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 6 (diagonal selection) and step 7 (applying criterion (C)), stated for an abstract double sequence. In the parent, A_{k,i} = blowUp T (x_i + λ_i y) (λ_i s_k) and Z_k = blowUp S y s_k. There (H1) is step 5, (H2) is hypothesis (c), and (H3) comes from steps 1–4.
The supplied step 6 also demands λ_{i(k)} < 1/(k+1) and |x_{i(k)} − x| < 1/(k+1). Its only purpose is to obtain the domain and mass bounds of step 7(a). Here those bounds are written directly into the diagonal conditions, as clause (b) below, using (H3).
Uses the sibling countable_tests = Submission.dimred_tr_ibl_countable_tests.

1. Let (ω_m)_{m∈ℕ} be the sequence in 𝒟ⁿ(ℝ^P) given by countable_tests for (P, n).
2. Using (H3), choose for every R ∈ ℕ numbers k₀(R) ∈ ℕ and Γ(R) ∈ [0, ∞) with:
 - M_{B_{R+1}(0)}(C) ≤ Γ(R);
 - for every k ≥ k₀(R) and all sufficiently large i, B_{R+1}(0) ⊆ V_{k,i} and M_{B_{R+1}(0)}(A_{k,i}) ≤ Γ(R).
3. For k, i ∈ ℕ let Q(k, i) be the conjunction of:
 - (a) |currentEval(A_{k,i}, ω_m) − currentEval(Z_k, ω_m)| < 1/(k+1) for every m ≤ k;
 - (b) for every R ≤ k with k₀(R) ≤ k: B_{R+1}(0) ⊆ V_{k,i} and M_{B_{R+1}(0)}(A_{k,i}) ≤ Γ(R).
4. For each fixed k, Q(k, i) holds for all sufficiently large i.
 - Clause (a), for one m ≤ k: (H1) with ω := ω_m gives currentEval(A_{k,i}, ω_m) → currentEval(Z_k, ω_m) as i → ∞. Since 1/(k+1) > 0, the inequality holds for all large i.
 - Clause (b), for one R ≤ k: if k₀(R) ≤ k it holds for all large i by step 2; if k₀(R) > k it holds vacuously.
 - Only finitely many m and R occur (m, R ∈ {0, …, k}). A finite intersection of sets of the form "for all large i" is again of that form (Filter.eventually_all_finite with the finite set {0, …, k}).
5. (Diagonal.) Apply the diagonal extraction lemma Filter.extraction_forall_of_eventually: if for every k the property Q(k, ·) holds for all large i, then there is a strictly increasing φ : ℕ → ℕ with Q(k, φ(k)) for every k. Fix such a φ and put D_k := A_{k,φ(k)} ∈ 𝒟_n(V_{k,φ(k)}).
6. (Mass hypothesis of countable_tests for D_k and C.) Let R ∈ ℕ, k₀' := max(k₀(R), R) and Γ := Γ(R) < ∞.
 - M_{B_{R+1}(0)}(C) ≤ Γ by step 2.
 - For k ≥ k₀' we have R ≤ k and k₀(R) ≤ k. So clause (b) of Q(k, φ(k)) gives B_{R+1}(0) ⊆ V_{k,φ(k)} and M_{B_{R+1}(0)}(D_k) ≤ Γ.
7. (Test hypothesis of countable_tests.) Fix m.
 - For k ≥ m, clause (a) of Q(k, φ(k)) gives |currentEval(D_k, ω_m) − currentEval(Z_k, ω_m)| < 1/(k+1). Since 1/(k+1) → 0, currentEval(D_k, ω_m) − currentEval(Z_k, ω_m) → 0 by squeezing.
 - By (H2) applied to ω_m ∈ 𝒟ⁿ(ℝ^P), currentEval(Z_k, ω_m) → C(ω_m).
 - Adding the two limits gives currentEval(D_k, ω_m) → C(ω_m).
8. Apply countable_tests with V_k := V_{k,φ(k)}, A_k := D_k and A := C. Its hypotheses are steps 6 and 7. So D_k ⇀ C in ℝ^P, i.e. ConvergesWeakly (fun k ↦ A_{k,φ(k)}) C. Together with the strict monotonicity of φ, this proves the claim. ∎
Lean note (not part of the proof): this argument compiles in about 35 lines against a stub of countable_tests with its frozen type. It uses choose on (H3), Filter.Eventually.and, Filter.eventually_all_finite (Set.finite_Iic k), Filter.extraction_forall_of_eventually, squeeze_zero_norm' with tendsto_one_div_add_atTop_nhds_zero_nat, and Tendsto.add.

## Key steps

1. Fix the countable test sequence (ω_m) of countable_tests and choose k₀(R), Γ(R) from (H3).
2. For each k, the finitely many conditions 'test values on ω_m within 1/(k+1) of those of Z_k for all m ≤ k' and 'domain and mass bounds for all R ≤ k with k₀(R) ≤ k' hold for all large i.
3. Filter.extraction_forall_of_eventually gives a strictly increasing φ satisfying all of them at i = φ(k).
4. Then D_k = A_{k,φ(k)} meets the mass hypothesis of countable_tests (k ≥ max(k₀(R), R)) and its test hypothesis (squeeze plus (H2)); so D_k ⇀ C.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem extraction_forall_of_eventually' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem Countable.exists_eq_range|lemma Countable.exists_eq_range' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem eventually_all_finite' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem tendsto_one_div_add_atTop_nhds_zero_nat' <snapshot>/mathlib/Mathlib; rg -ln "squeeze_zero_norm'" <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem secondCountable_of_countable_discretization' <snapshot>/mathlib/Mathlib`
- `rg -n 'tsupport_sub' <snapshot>/mathlib/Mathlib (only tsupport_subset hits; tsupport_sub is the to_additive form, confirmed by compiling)`
- `rg -n 'dimred_tr_ibl|dimred_tr_countable_tests|dimred_tr_iterated_blowup_limit' <snapshot>/project GMT .lake/packages/simongmt/Poincare --glob '*.lean' (exit 1, no match)`
- `rg -n 'def currentEval|def ConvergesWeakly|def blowUp|def dilation ' <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.le_massOn|def massAdmissibleOn|def covectorEuclideanNorm' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `rg -n 'theorem affinePullbackForm_isTestForm|def GeometricCurrentOn.affinePushforward' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `python3 scans of dag.json: accepted lean_statements mentioning massOn/ConvergesWeakly/dilation ⁻¹' ball/covectorEuclideanNorm/testForm; status, candidate_commit and lean_name reservations`
- `python3 /tmp/ibl-split/scripts/check_reuse.py (git show <candidate>:GMT/Ch07/Submission.lean; declared type vs dag.json type; sorry count)`
- `lake env lean /tmp/ibl-split/cands/<name>.lean (#print axioms of the five reused declarations at their candidates)`
- `lake env lean /tmp/ibl-split/lean/Assembly.lean (new children and parent from exact-type stubs)`
- `python3 -I /tmp/ibl-split/mkchallenge.py (verifier lean_contract.validate_lean_statement and gmt-compare child_modules, contract mode); lake env lean /tmp/ibl-split/challenge/<key>_Challenge.lean`
- `python3 /tmp/ibl-split/validate.py (replica of runtime _dependency_problem and _existing_lean_name_problem)`
- `reading of runtime.py (_overlay_accepted_children, _solve_children, _existing_lean_name_problem), inherited.py and prompts.py of /runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean`
- `python3 reading of the grandparent's decomposition-v4.json/v5.json (countable_tests child and its merge rationale) and of the reused nodes' parent-supplied-natural-proof.md and isolated-comparator-result.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-iterated-b-94298ffd19/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-t-9b84f5afc6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-t-9b84f5afc6/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c658ab2df9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c658ab2df9/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-95c10b37fe/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-95c10b37fe/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/prompts.py`
- `/tmp/ibl-split/lean/Assembly.lean`
- `/tmp/ibl-split/cands/dor_lmbs_testForm_countable_approx.lean`
- `/tmp/ibl-split/challenge/countable_tests_Challenge.lean`
- `/tmp/ibl-split/challenge/diagonal_limit_Challenge.lean`
- `/tmp/ibl-split/validate.py`

Pins match. The snapshot manifest records project b4d606d and mathlib 25730c7c, equal to the workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library facts cited by the new children exist in the snapshot mathlib:
- Filter.extraction_forall_of_eventually (Order/Filter/AtTopBot/Basic.lean:135);
- Set.Countable.exists_eq_range (Data/Set/Countable.lean:149);
- Filter.eventually_all_finite (Order/Filter/Finite.lean:252);
- tendsto_one_div_add_atTop_nhds_zero_nat (Analysis/SpecificLimits/Basic.lean:70);
- Metric.secondCountable_of_countable_discretization (Topology/MetricSpace/Basic.lean:168).
tsupport_sub has no textual hit; it is generated by to_additive, and the compiled proofs use it.

The contract's currentEval, ConvergesWeakly, blowUp and dilation, and SimonGMT's massOn, le_massOn, massAdmissibleOn, covectorEuclideanNorm and affinePullbackForm_isTestForm, are as the proofs use them.

Names: no dimred_tr_ibl_* declaration exists in the snapshot, GMT, SimonGMT or dag.json.

Reused declarations: dor_lmbs_testForm_countable_approx, rsd_mw_tfa_norm_props, cmr_abs_apply_le_massOn, idtp_convergesWeakly_massOn_le and dtc_bc_cz_blowUp_eval_dilation_ball are accepted. Their child lean_statements are string-identical to dag.json. Their candidates keep the frozen imports, passed isolated comparators, and recompile with only propext, Classical.choice and Quot.sound.

Lean checks:
- All 7 types pass the verifier's statement validator, and their comparator challenge files elaborate.
- The new children and the exact selected type compile from exact-type stubs of the five reused children and dimred_tr_blowup_calculus (exit 0; sorry only in the stubs).
