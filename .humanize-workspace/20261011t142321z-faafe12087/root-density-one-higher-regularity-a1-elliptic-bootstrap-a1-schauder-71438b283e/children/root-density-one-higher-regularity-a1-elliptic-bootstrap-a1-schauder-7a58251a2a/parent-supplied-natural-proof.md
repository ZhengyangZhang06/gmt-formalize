# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1.unif_of_dense-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2d-e of the parent proof. That step cites the Arzela-Ascoli theorem BoundedContinuousFunction.arzela_ascoli. Its module Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli is not imported by the frozen contract, so the classical proof is supplied here: the uniform Hoelder bound (equicontinuity) upgrades convergence on a dense subset of a compact set to uniform convergence.
1. Limits on D. For d in D let v(d) be the limit of F_j(d).
2. A Hoelder scale. Let epsilon > 0. The function t -> K t^alpha is continuous at t = 0, because alpha > 0, and its value there is K * 0^alpha = 0. (Real.continuousAt_rpow_const 0 alpha, using 0 <= alpha, and Real.zero_rpow.) So there is delta > 0 with K t^alpha < epsilon/3 whenever |t| < delta (Metric.eventually_nhds_iff). Put eta := delta/2 > 0; only this positive value t = eta is used below. Then K eta^alpha < epsilon/3.
3. A finite net inside D. Let z in S. Since z lies in the closure of D, there is d in D with |z - d| < eta. Hence the open balls B_eta(d), d in D, cover S. S is compact, so finitely many of them cover S (IsCompact.elim_finite_subcover_image; Metric.mem_closure_iff for the cover): there is a finite subset T of D with S contained in the union of the balls B_eta(d), d in T.
4. Cauchy at the net points. T is finite and F_j(d) -> v(d) for every d in T. So there is N with ||F_j(d) - v(d)|| < epsilon/6 for all j >= N and all d in T (Set.Finite.eventually_all, then eventually_atTop). Then ||F_j(d) - F_{j'}(d)|| <= ||F_j(d) - v(d)|| + ||F_{j'}(d) - v(d)|| < epsilon/3 for all j, j' >= N and d in T.
5. Uniform Cauchy estimate. Let j, j' >= N and z in S. Pick d in T with |z - d| < eta. Since d lies in D, a subset of S, the Hoelder hypothesis applies to z and d: ||F_j(z) - F_j(d)|| <= K |z - d|^alpha <= K eta^alpha < epsilon/3. This uses that t -> t^alpha is monotone on [0, infinity) and that K >= 0. Likewise ||F_{j'}(d) - F_{j'}(z)|| < epsilon/3. By the triangle inequality, ||F_j(z) - F_{j'}(z)|| < epsilon/3 + epsilon/3 + epsilon/3 = epsilon. So (F_j) is uniformly Cauchy on S (Metric.uniformCauchySeqOn_iff).
6. The limit function. For z in S the sequence (F_j(z)) is Cauchy in L. L is complete, being a finite-dimensional normed space, so the sequence converges (UniformCauchySeqOn.cauchySeq, cauchySeq_tendsto_of_complete, tendsto_nhds_limUnder). Let G(z) be the limit of F_j(z) whenever it exists (for instance limUnder atTop), and arbitrary otherwise. Then F_j(z) -> G(z) for every z in S.
7. Uniform convergence. Let epsilon > 0 and take N as in step 5. For j >= N and z in S we have ||F_j(z) - F_{j'}(z)|| < epsilon for every j' >= N. Letting j' -> infinity gives ||F_j(z) - G(z)|| <= epsilon. This holds for all j >= N and all z in S, so F_j -> G uniformly on S (in Mathlib: UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto). QED.

## Key steps

1. choose eta > 0 with K eta^alpha < epsilon/3, using continuity of t -> K t^alpha at 0
2. by compactness, finitely many balls B_eta(d) with centres d in a finite subset T of D cover S
3. the finitely many convergent sequences F_j(d), d in T, are simultaneously epsilon/3-Cauchy from some N on
4. the triangle inequality and the Hoelder bound give the uniform Cauchy estimate on S
5. L is complete, so a pointwise limit G exists on S; uniformly Cauchy plus pointwise convergence gives uniform convergence

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -l -i '\barzela|\bascoli\b|ArzelaAscoli' <snapshot>/mathlib/Mathlib <snapshot>/project`
- `rg -n -i 'diagonal (sub)?sequence|diagonal extraction|extraction_forall_of_frequently|extraction_of_frequently_atTop|extraction_forall_of_eventually' <snapshot>/mathlib/Mathlib <snapshot>/project`
- `rg -n -i 'arzela|ascoli|diagonal|equicontinu|subsequence' <snapshot>/project --glob '*.lean'`
- `rg -n -i 'ascoli' <snapshot>/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean`
- `rg -n 'theorem arzela_ascoli|theorem tendstoUniformlyOn_singleton_iff_tendsto|theorem UniformCauchySeqOn.cauchySeq|theorem tendstoUniformlyOn_empty|theorem TendstoUniformlyOn.congr_right|theorem IsSeparable.exists_countable_dense_subset|theorem exists_countable_dense_subset|theorem Countable.exists_eq_range|theorem exists_dense_seq|theorem IsCompact.tendsto_subseq|theorem UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem uniformCauchySeqOn_iff|theorem IsCompact.elim_finite_subcover_image|theorem continuousAt_rpow_const|theorem TendstoUniformlyOn.congr |theorem tendsto_nhds_limUnder|theorem cauchySeq_tendsto_of_complete|theorem strictMono_nat_of_lt_succ|theorem StrictMono.id_le|theorem eventually_all_finite|theorem TendstoUniformlyOn.tendsto_at|theorem le_of_tendsto |instance.*proper_real|theorem mem_closure_iff ' <snapshot>/mathlib/Mathlib`
- `lean after `import GMT.Ch05.Submission`: #eval env.getModuleIdx? for Mathlib.Topology.UniformSpace.Ascoli, Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli, Mathlib.Topology.MetricSpace.Sequences, Mathlib.Topology.Sequences, Mathlib.Topology.UniformSpace.UniformConvergence, Mathlib.Topology.UniformSpace.Equicontinuity, Mathlib.Topology.UniformSpace.CompactConvergence`
- `lean #check BoundedContinuousFunction.arzela_ascoli / ArzelaAscoli.isCompact_of_equicontinuous / tendsto_subseq_of_bounded / IsCompact.tendsto_subseq / Metric.uniformCauchySeqOn_iff / TopologicalSpace.exists_countable_dense_subset and inferInstance for ProperSpace, FirstCountableTopology, CompleteSpace, SeparableSpace on Rn n and Rn n →L[ℝ] Rn ℓ`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') -> replayed child scope`
- `python3 scan of dag.json: lean_name collisions for dohr_eb_sch_bu_hds_*, accepted nodes whose types mention StrictMono/TendstoUniformlyOn/UniformCauchySeqOn, depth and status of the selected node and its siblings`
- `grep max_depth /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; read check_source_delta in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `lean checks in /tmp/hds-decomp: Challenge_<name>.lean (5 frozen types), Split.lean (full proofs + #print axioms), AsmParent.lean, AsmCompact.lean, Inst.lean, node/Solution_<name>.lean against the Submission_with_split build; python3 leafsim.py (check_source_delta replay)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Ascoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-71438b283e/parent-child-handoff.json`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean.

Arzela-Ascoli is not usable by any child. Pinned Mathlib contains BoundedContinuousFunction.arzela_ascoli (Topology/ContinuousMap/Bounded/ArzelaAscoli.lean:109) and ArzelaAscoli.isCompact_of_equicontinuous (Topology/UniformSpace/Ascoli.lean). Neither module, nor Topology/MetricSpace/Sequences.lean, is transitively imported by the frozen contract: getModuleIdx? returns none and #check reports unknown constants. Leaves cannot add imports, so the parent's step 2d citation is replaced by the children's classical proof.

Available under the contract imports and used by the compiled child proofs:
- IsCompact.tendsto_subseq (Topology/Sequences.lean:298)
- In UniformConvergence.lean: tendstoUniformlyOn_singleton_iff_tendsto (:327), tendstoUniformlyOn_empty (:324), TendstoUniformlyOn.congr (:196), TendstoUniformlyOn.congr_right (:218), TendstoUniformlyOn.tendsto_at (:154), UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (:499), UniformCauchySeqOn.cauchySeq (:573)
- Metric.uniformCauchySeqOn_iff (Topology/MetricSpace/Cauchy.lean:70)
- TopologicalSpace.exists_countable_dense_subset (Topology/Bases.lean:353)
- Set.Countable.exists_eq_range (Data/Set/Countable.lean:149)
- IsCompact.elim_finite_subcover_image (Topology/Compactness/Compact.lean:347)
- Filter.eventually_all_finite (Order/Filter/Finite.lean:252)
- cauchySeq_tendsto_of_complete (Topology/UniformSpace/Cauchy.lean:425)
- tendsto_nhds_limUnder (Topology/Basic.lean:245)
- Real.continuousAt_rpow_const (Analysis/SpecialFunctions/Pow/Continuity.lean:220)
- StrictMono.id_le (Order/WellFounded.lean:267)
- strictMono_nat_of_lt_succ (Order/Monotone/Basic.lean:569)
- Metric.mem_closure_iff (Topology/MetricSpace/Pseudo/Defs.lean:1220)
- le_of_tendsto (Topology/Order/OrderClosed.lean:133)
- the FiniteDimensional.proper_real instance (Analysis/Normed/Module/FiniteDimension.lean:554)

Filter.extraction_forall_of_frequently (Order/Filter/AtTopBot/Basic.lean:123) is a pointwise extraction and does not give a diagonal for uniform convergence on sets. The project snapshot has no Arzela-Ascoli, equicontinuity-upgrade or diagonal-subsequence lemma; its only subsequence hits are unrelated prose in Ch01, Ch02 and Ch08.

dag.json has no node named dohr_eb_sch_bu_hds_* and no accepted node with any of the proposed types. The selected node is at depth 5 and max_depth is 6, so the children are leaves.

Lean evidence:
- All child types elaborate in the replayed comparator scope.
- Full single-theorem proofs of the four children and the parent assembly compile with axioms [propext, Classical.choice, Quot.sound].
- The parent is proved from the three child types as axioms.
- The NodeSolution checks and the check_source_delta replay pass.
- Instances confirmed by rfl: ^ is Real.rpow, and L carries the operator-norm uniformity.

The evidence is in GMT/Scratch/dohr_eb_sch_bu_hds/.
