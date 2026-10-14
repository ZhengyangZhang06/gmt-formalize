# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.weak_compactness-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.weak_compactness-a1.limit_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (C is a current in ℝ^P): linearity of the pointwise limit by uniqueness of limits, the bound |C(ω)| ≤ c·s as the limit of the uniform bounds, and sequential continuity derived from that bound; the last part is exactly the accepted sibling order_zero_current. Sibling used: order_zero_current (accepted declaration cmcs_rc_order_zero_current).

Notation. All test forms are elements of TestFormOn univ n; ω(x) is the value of the underlying form and ‖·‖ is the operator norm on Covector (Euclid P) n.

1. (The pointwise limit.) By (b), for every test form ω choose L(ω) ∈ ℝ with S_i(ω) → L(ω) as i → ∞. Limits of real sequences are unique (tendsto_nhds_unique, ℝ is Hausdorff and atTop on ℕ is a proper filter).
2. (Additivity.) Let ω, η be test forms. Each S_i is linear, so S_i(ω + η) = S_i(ω) + S_i(η) → L(ω) + L(η) (Tendsto.add). Also S_i(ω + η) → L(ω + η) by step 1. By uniqueness of limits, L(ω + η) = L(ω) + L(η).
3. (Homogeneity.) Let a ∈ ℝ and ω a test form. Then S_i(a·ω) = a·S_i(ω) → a·L(ω) (Tendsto.const_mul), and S_i(a·ω) → L(a·ω). Hence L(a·ω) = a·L(ω). By steps 2–3, L is an ℝ-linear map TestFormOn univ n →ₗ[ℝ] ℝ.
4. (Zeroth-order bounds for L.) Let K ⊆ ℝ^P be compact (trivially K ⊆ univ) and let c ≥ 0 be given by (a). Let ω be a test form with tsupport ω ⊆ K and M ∈ ℝ with ‖ω(x)‖ ≤ M for all x. By (a), |S_i(ω)| ≤ c·M for every i. By continuity of the absolute value, |S_i(ω)| → |L(ω)| (Tendsto.abs), and a limit of terms all ≤ c·M is ≤ c·M (le_of_tendsto'). Hence |L(ω)| ≤ c·M.
5. (L is a current.) Step 4 is precisely the hypothesis of order_zero_current for U := univ and the linear map L of step 3: for every compact K ⊆ univ there is c ∈ ℝ with |L(ω)| ≤ c·M whenever tsupport ω ⊆ K and ‖ω(x)‖ ≤ M for all x. Therefore order_zero_current yields C ∈ GeometricCurrentOn univ n with C(ω) = L(ω) for every test form ω.
6. (Weak convergence.) For every test form ω, S_i(ω) → L(ω) = C(ω) by steps 1 and 5. This is WeaklyConvergesOn S C. ∎

## Key steps

1. Let L(ω) := lim_i S_i(ω).
2. Uniqueness of limits makes L ℝ-linear.
3. Passing to the limit in (a) gives |L(ω)| ≤ c·M when tsupport ω ⊆ K and ‖ω(x)‖ ≤ M for all x.
4. order_zero_current turns L into a current C with C(ω) = L(ω), so S_i(ω) → C(ω) for every ω.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed -n 1,140p GMT/Ch07/Submission.lean; cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Mass,FormSupNorm,Forms,Currents}.lean (GeometricCurrentOn, TestFormOnConverges, WeaklyConvergesOn, massOn, massAdmissibleOn, le_massOn, covectorEuclideanNorm)`
- `python3 -I over dag.json lean_statement fields: regexes for '|T ω| ≤' and 'massOn W).toReal'; keywords Countable, StrictMono, TestFormOnConverges, Dense, CauchySeq; covectorEuclideanNorm together with ‖; '→ₗ[ℝ] ℝ'; 'Bornology.IsBounded W → ⨆'; lean_name prefix dtc_bc_tc_wc; status, candidate_commit, children and depends_on closure of the five reused nodes`
- `git cat-file -t <commit>; git show <commit>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name> :' (exact type comparison) for cmr_abs_apply_le_massOn 7a706164, rsd_mw_tfa_norm_props f492ba4a, dor_lmbs_testForm_countable_approx b7ecbda9, codim1_zsl_pc_diagonal_subseq 0108f792, cmcs_rc_order_zero_current 49358939, dpf_pfc_testFormOnConverges_zero_uniform 8d68dfd9`
- `rg -n -l 'dtc_bc_tc_wc' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib lake-packages-25730c7c/simongmt GMT; git log --all --oneline -S dtc_bc_tc_wc`
- `rg -n -e "(theorem|lemma) (Continuous\.bounded_above_of_compact_support|cauchySeq_tendsto_of_complete|tendsto_nhds_unique|tsupport_sub|tendsto_nhds_limUnder|le_of_tendsto'|toReal_mono|Countable\.to_subtype|IsBounded\.subset_ball|IsCompact\.isBounded|cauchySeq_iff|tendstoUniformly_iff|HasCompactSupport\.isCompact)( |$)" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/wc_check/Probe.lean: #check Continuous.bounded_above_of_compact_support, cauchySeq_tendsto_of_complete, Metric.cauchySeq_iff, tendsto_nhds_unique, Set.Countable.to_subtype, Bornology.IsBounded.subset_ball, IsCompact.isBounded, tsupport_sub, Metric.tendstoUniformly_iff, tendsto_nhds_limUnder, ENNReal.toReal_mono, le_iSup, norm_iteratedFDeriv_zero, le_of_tendsto', HasCompactSupport.isCompact, closure_minimal, isOpen_ball, isBounded_ball`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope + child_modules (contract mode) on the 8 types; lake env lean /tmp/wc_check/challenges/Challenge_<name>.lean (8 files) and /tmp/wc_check/Assembly.lean with #print axioms`
- `sed -n 305,335p book/chapter-06.txt; sed -n 878,895p book/chapter-06.txt`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|existing_by_name' /runtime/flows/gmt-claude-5675b49b7aec/_recursive_lean/runtime.py; grep -o '"max_nodes": *[0-9]*' .humanize/swarm-configs/*.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f2009ef820/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f2009ef820/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-t-9b84f5afc6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-e85e0715a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-restrict-curren-7244aadae8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-5675b49b7aec/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/wc_check/Assembly.lean`
- `/tmp/wc_check/Probe.lean`
- `/tmp/wc_check/types.py`

Snapshot mode local-project (project b4d606db, Mathlib 25730c7c). The workspace Submission.lean and the pinned SimonGMT Chapter06 files fix the objects of the selected type: GeometricCurrentOn univ n is a linear map on TestFormOn univ n together with sequential continuity for TestFormOnConverges ωs 0; WeaklyConvergesOn is pointwise convergence; massOn is the sSup over massAdmissibleOn with the Euclidean coefficient norm. Five comparator-accepted DAG declarations state steps of the supplied proof, and each is reused with a type identical to its DAG lean_statement and to its candidate commit: cmr_abs_apply_le_massOn (step 1), rsd_mw_tfa_norm_props (|α| ≤ N‖α‖), dor_lmbs_testForm_countable_approx (step 2; accepted children compact_exhaustion, covector_findim, fixed_support_dense), codim1_zsl_pc_diagonal_subseq (step 3) and cmcs_rc_order_zero_current (continuity in step 5). dpf_pfc_testFormOnConverges_zero_uniform also fits step 5 but is not needed once order_zero_current is used. The twin dimred_mbl_tc_weak_compactness is queued and has a different (ball-only) hypothesis, so it is not reusable. No accepted declaration states local_bound, dense_extension or limit_current. No dtc_bc_tc_wc name occurs in the DAG, the snapshot project, the snapshot Mathlib, SimonGMT, the workspace GMT sources or git history. Every Mathlib lemma used by the assembly and the new children exists in the snapshot Mathlib, e.g. Continuous.bounded_above_of_compact_support (Analysis/Normed/Group/Bounded.lean:153), cauchySeq_tendsto_of_complete (Topology/UniformSpace/Cauchy.lean:425), tendsto_nhds_unique (Topology/Separation/Hausdorff.lean:180), Metric.tendstoUniformly_iff (Topology/MetricSpace/Pseudo/Basic.lean:157), le_of_tendsto' (Topology/Order/OrderClosed.lean:138) and ENNReal.toReal_mono (Basic/ENNReal/Real.lean:67). All were also confirmed by #check in the pinned environment. All 8 child types elaborate in comparator contract scope. The parent assembly from the five direct children, and the proofs of the three new children from their declared siblings, compile using only propext, Classical.choice and Quot.sound.
