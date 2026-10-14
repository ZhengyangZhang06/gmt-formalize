# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1.nonneg_fundamental_lemma-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the analytic core of step 3 of the parent-supplied proof of `codim1_rdo_dg_halfspace_rigidity` (“This forces f := u(· + tv) − u ≥ 0 a.e.”), stated for an arbitrary locally integrable f. The parent approximates 1_S, S = {f < 0} ∩ B_R(0), by mollified indicators η_{1/j} * 1_S. This proof makes the same three moves:
- approximate an indicator by admissible nonnegative test functions bounded by 1 with uniformly compact supports;
- pass to the limit by dominated convergence;
- conclude from the sign of f on S.
The approximants are smooth Urysohn functions of compact sets K ⊆ S, followed by inner regularity. This is only a change of execution detail: the mollifier API (`ContDiffBump.normed`, `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`) is not in the import closure of `GMT.Ch07.Submission` (both are unknown constants there), whereas the smooth Urysohn lemma and inner regularity are. The scheme mirrors Mathlib's own proof of `ae_eq_zero_of_integral_contMDiff_smul_eq_zero` (Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean).

Notation.
- E := ℝⁿ, L := Lⁿ.
- B_R := the open ball of radius R about 0.
- For K ⊆ E and r > 0: K_r := {x : dist(x, K) < r} (open thickening, Mathlib `thickening r K`) and K^r := {x : dist(x, K) ≤ r} (closed thickening, `cthickening r K`).

1. Integrals over compact sets are nonnegative: ∫_K f ≥ 0 for every compact K ⊆ E.
   - Let K be compact. The closed thickening K^1 is closed and bounded, hence compact (Mathlib `IsCompact.cthickening`).
   - Put u_j := 1/(j + 2) ∈ (0, 1) for j ∈ ℕ, so u_j → 0.
   - For each j, K is closed, K_{u_j} is open (`isOpen_thickening`) and K ⊆ K_{u_j} (`self_subset_thickening`).
   - By the smooth Urysohn lemma (Mathlib `exists_contMDiff_support_eq_eq_one_iff` for the model 𝓘(ℝ, E), converted with `contMDiff_iff_contDiff`), there is a C^∞ function g_j : E → ℝ with values in [0, 1], support g_j = K_{u_j}, and g_j = 1 on K.
   - Then g_j is C¹ and g_j ≥ 0. Also tsupport g_j = closure(K_{u_j}) ⊆ K^{u_j} ⊆ K^1 (`closure_thickening_subset_cthickening`, monotonicity in the radius), so g_j has compact support.
   - By hypothesis, ∫ g_j f ≥ 0 for every j.

2. Pointwise convergence. Fix x.
   - If x ∈ K, then g_j(x) = 1 = 1_K(x) for all j.
   - If x ∉ K: since K is closed, K = closure K = ⋂_{ε>0} K_ε (Mathlib `closure_eq_iInter_thickening`), so there is ε > 0 with x ∉ K_ε (this also covers K = ∅, where every K_ε is empty). For every j with u_j < ε (all large j, as u_j → 0) we have K_{u_j} ⊆ K_ε, so x ∉ K_{u_j} = support g_j and g_j(x) = 0 = 1_K(x).
   - Hence g_j(x) f(x) → 1_K(x) f(x) for every x.

3. Dominated convergence.
   - For all j and x, |g_j(x) f(x)| ≤ 1_{K^1}(x)·|f(x)|, since 0 ≤ g_j ≤ 1 and g_j = 0 off K^1.
   - The bound is integrable because f is locally integrable and K^1 is compact (Mathlib `LocallyIntegrable.integrableOn_isCompact`).
   - Each g_j f is a.e. strongly measurable (a continuous function times an a.e. strongly measurable one).
   - By dominated convergence (Mathlib `tendsto_integral_of_dominated_convergence`), ∫ g_j f → ∫ 1_K f = ∫_K f (Mathlib `integral_indicator`; K is closed, hence measurable).
   - Every ∫ g_j f ≥ 0, so ∫_K f ≥ 0.

4. A Borel representative.
   - f is locally integrable, hence a.e. strongly measurable. Let f̃ := `AEStronglyMeasurable.mk f`, a measurable function with f̃ = f L-a.e.
   - f̃ is locally integrable (`LocallyIntegrable.congr`), and set integrals are unchanged: ∫_K f̃ = ∫_K f ≥ 0 for every compact K, by step 1.
   - It suffices to prove f̃ ≥ 0 L-a.e.

5. The negative set is null in each ball.
   - Fix R ∈ ℕ and let S := {x : f̃(x) < 0} ∩ B_R. S is measurable and L(S) ≤ L(B_R) < ∞.
   - Suppose L(S) > 0. Lebesgue measure is inner regular on sets of finite measure (Mathlib `MeasurableSet.exists_lt_isCompact_of_ne_top`, applied with r := 0 < L(S)), so there is a compact K ⊆ S with L(K) > 0.
   - Let h := 1_K·(−f̃). Then h is integrable (f̃ is integrable on the compact K) and h ≥ 0 everywhere, since f̃ < 0 on K.
   - The support of h is exactly K (−f̃ > 0 on K), which has positive measure. By Mathlib `integral_pos_iff_support_of_nonneg`, ∫ h > 0, i.e. ∫_K f̃ < 0.
   - This contradicts step 4. Hence L(S) = 0.

6. Conclusion. {f̃ < 0} = ⋃_{R∈ℕ} ({f̃ < 0} ∩ B_R) is a countable union of L-null sets, hence L-null (`measure_iUnion_null`). So f̃ ≥ 0 L-a.e., and since f = f̃ L-a.e., f ≥ 0 L-a.e. ∎

## Key steps

1. For compact K, smooth Urysohn functions g_j (0 ≤ g_j ≤ 1, g_j = 1 on K, support g_j = the u_j-thickening of K, u_j ↓ 0) are admissible nonnegative C¹_c tests, so ∫ g_j f ≥ 0.
2. g_j → 1_K pointwise and |g_j f| ≤ |f|·1_{K^1}; dominated convergence gives ∫_K f ≥ 0 for every compact K.
3. Pass to a measurable representative f̃. If S = {f̃ < 0} ∩ B_R had positive measure, inner regularity would give a compact K ⊆ S with L(K) > 0 and ∫_K f̃ < 0, a contradiction.
4. The countable union over R ∈ ℕ gives f̃ ≥ 0 a.e., hence f ≥ 0 a.e.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sha256sum of snapshot vs .lake/packages/mathlib for AEEqOfIntegralContDiff.lean, AEEqOfIntegral.lean, Besicovitch.lean, EqHaar.lean, PartitionOfUnity.lean, Integral/Prod.lean, FDeriv/Const.lean (all SAME)`
- `rg -n "theorem ae_eq_of_integral_contDiff_smul_eq|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem ae_nonneg_of_forall_setIntegral_nonneg|theorem ae_le_of_forall_setIntegral_le|theorem ae_nonneg_of_forall_setIntegral_nonneg_of|theorem ae_eq_zero_of_forall_setIntegral_isCompact|isCompact.*nonneg|theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg" mathlib/Mathlib`
- `sed -n 60,215p mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean; sed -n 120,215p and 340,430p mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `rg -n --glob '*.lean' "theorem .*(halfspace|half_space|halfSpace)" project mathlib/Mathlib/Analysis mathlib/Mathlib/MeasureTheory`
- `rg -n --glob '*.lean' "theorem .*(ae_nonneg_of_integral|integral_contDiff.*nonneg|nonneg_of_integral_contDiff|ae_translate|translate_invariant|ae_add_right_invariant)" project mathlib/Mathlib (no match)`
- `rg -n --glob '*.lean' "theorem .*(halfspace|half_space|translat|ae_nonneg|density_point|lebesgue_density|integral_contDiff)" lake-packages-25730c7c/simongmt (no match)`
- `rg -n "theorem ae_tendsto_measure_inter_div_of_measurableSet|theorem addHaar_affineSubspace|intervalIntegral_integral_swap|theorem exists_contMDiff_support_eq_eq_one_iff|theorem support_fderiv_subset" mathlib/Mathlib`
- `python3 scans of dag.json: status counts (1010 nodes), lean_name hits for the five codim1_rdo_dg_hr_* names (none), identical frozen types (none), similar statements (fderiv+HasCompactSupport+∀ᵐ, symmDiff, 0 ≤ ∫+ContDiff); scan of 925 nodes/*/decomposition-v*.json and decomposition-review-retry.json for the names (only this node's never-activated decomposition-v1.json)`
- `cat nodes/<this node>/{decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json,decomposition-scope-v1.json,parent-child-handoff.json}`
- `sed -n 1000,1100p, 1388,1640p, 1800,1990p, 2760,2900p, 6532,6590p runtime.py (_decompose, _solve_children node bound, _install_speculative_assumptions, _existing_lean_name_problem); grep 'Unknown identifier .Euclid' nodes/*/speculative-process-v*.log`
- `sed -n 655,692p book/chapter-03.txt (Simon Ch. 3, 4.3 (7)-(9))`
- `lake env lean -DautoImplicit=false /tmp/hr-split-v2/Types.lean (5 child types + parent frozen type proved from them; #print axioms)`
- `lake env lean /tmp/hr-split-v2/Stub.lean and /tmp/hr-split-v2/StubAssembly.lean (replica of controller speculative stub; parent proved against stub axioms)`
- `lake env lean /tmp/hr-split-v2/{Parse,Avail,Avail2,Avail3,Inst}.lean (rfl parse checks; availability of every cited lemma; ContDiffBump.normed and ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable unknown; instances for general n)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-03acf74a7a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-03acf74a7a/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-03acf74a7a/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/speculative-process-v1.log`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt`
- `/tmp/hr-split-v2/Types.lean`
- `/tmp/hr-split-v2/Stub.lean`
- `/tmp/hr-split-v2/StubAssembly.lean`
- `/tmp/hr-split-v2/Parse.lean`
- `/tmp/hr-split-v2/Avail.lean`
- `/tmp/hr-split-v2/Avail2.lean`
- `/tmp/hr-split-v2/Avail3.lean`
- `/tmp/hr-split-v2/Inst.lean`

Pins and identity checks:
- Snapshot manifest: project b4d606db, Mathlib 25730c7c. Both match the workspace HEAD and .lake/packages/mathlib. SimonGMT is pinned at 2b366308.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
- Every cited Mathlib file in the snapshot is byte-identical to the workspace package.

Library results used by the children:
- Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet (Besicovitch.lean:1089)
- Measure.addHaar_affineSubspace (EqHaar.lean:199)
- exists_contMDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:755)
- intervalIntegral_integral_swap (Integral/Prod.lean:483)
- support_fderiv_subset (FDeriv/Const.lean:379)
- ae_eq_of_integral_contDiff_smul_eq (AEEqOfIntegralContDiff.lean:195)
- MeasurableSet.exists_lt_isCompact_of_ne_top, integral_pos_iff_support_of_nonneg, measure_preimage_add_right, integral_add_right_eq_self

What is missing:
- There is no nonnegative-test version of the fundamental lemma. AEEqOfIntegral.lean:130 requires global integrability.
- No translation identity, half-space rigidity or density-trichotomy lemma exists in Mathlib, the project or SimonGMT (rg found no match).
- ContDiffBump.normed and the mollifier convergence lemma are not in the import closure of GMT.Ch07.Submission.

Lean checks:
- All 5 child types elaborate after `import GMT.Ch07.Submission`, both in GMT.Ch07 scope and in the replicated speculative stub (root namespace Submission, regex-selected opens).
- Children use EuclideanSpace ℝ (Fin n) because speculative logs show `Euclid` failing in the stub.
- The parent's exact frozen type is proved from the children, with step 4 formalized. #print axioms gives propext, sorryAx, Classical.choice, Quot.sound; against stub axioms it gives only those three plus the three consumer-child axioms.

Names and reuse:
- The five codim1_rdo_dg_hr_* names occur in no DAG node (1010 nodes). The only file containing them is this node's never-activated decomposition-v1.json, which carries the identical audited split.
- No accepted node has an identical frozen type, so nothing is reused.

Source: the printed Simon Ch. 3, 4.3 (8)–(9) text is confirmed at chapter-03.txt lines 664–690.
