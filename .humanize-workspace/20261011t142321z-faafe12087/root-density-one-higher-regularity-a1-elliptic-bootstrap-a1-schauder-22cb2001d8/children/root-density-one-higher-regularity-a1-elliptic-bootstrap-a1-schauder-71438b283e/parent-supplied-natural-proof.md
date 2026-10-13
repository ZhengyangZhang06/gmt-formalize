# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the Arzela-Ascoli and diagonal-subsequence part of step 7 of the parent proof, stated for a general sequence (there f_k = DW_k).
1. Uniform bounds. For m in N put B^m := Bbar_m(0), a compact set because R^n is proper. Since R_k -> infinity, there is k_m in N with R_k > m for all k >= k_m. Let k >= k_m and z, z' in B^m. Then z, z' and 0 lie in B_{R_k}(0), so ||f_k(z) - f_k(z')|| <= K |z - z'|^alpha. Also ||f_k(z)|| = ||f_k(z) - f_k(0)|| <= K |z|^alpha <= K m^alpha, since t -> t^alpha is monotone on [0, infinity) for alpha > 0.
2. Arzela-Ascoli step. Claim: for every m in N and every strictly increasing psi : N -> N there are a strictly increasing chi : N -> N and g : R^n -> L with f_{psi(chi(j))} -> g uniformly on B^m.
 a. Put j0 := k_m. Since psi(i) >= i for all i, psi(j0 + j) >= k_m for every j.
 b. Let h_j be the restriction of f_{psi(j0 + j)} to B^m, a compact space in the subspace topology. By step 1, h_j is continuous (indeed Hoelder) with values in the closed ball of radius K m^alpha in L. That ball is compact because L is finite-dimensional. So h_j is a bounded continuous function.
 c. The family (h_j) is equicontinuous. Given epsilon > 0, choose eta > 0 with K eta^alpha < epsilon. Then |z - z'| < eta implies ||h_j(z) - h_j(z')|| <= K |z - z'|^alpha <= K eta^alpha < epsilon for all j.
 d. By the Arzela-Ascoli theorem (BoundedContinuousFunction.arzela_ascoli), the closure of {h_j : j in N} in the space of bounded continuous functions B^m -> L with the sup metric is compact.
 e. A sequence in a compact metric space has a convergent subsequence (IsCompact.tendsto_subseq). So there are a strictly increasing chi' and a bounded continuous h with sup over B^m of ||h_{chi'(j)} - h|| -> 0.
 f. Put chi(j) := j0 + chi'(j), which is strictly increasing. Let g := h on B^m and g := 0 elsewhere. Then sup over z in B^m of ||f_{psi(chi(j))}(z) - g(z)|| -> 0, which is uniform convergence on B^m.
3. Diagonal construction. Choose strictly increasing chi_0, chi_1, ... recursively with step 2:
 a. chi_m comes from step 2 applied to m and psi_{m-1}, where psi_{-1} := id and psi_m := psi_{m-1} o chi_m = chi_0 o ... o chi_m.
 b. Thus each psi_m is strictly increasing, and f_{psi_m(j)} converges uniformly on B^m as j -> infinity, to a limit g_m.
 c. Define phi(j) := psi_j(j).
4. phi is strictly increasing. A strictly increasing map chi : N -> N satisfies chi(i) >= i, so chi_{j+1}(j+1) >= j+1 > j. Since psi_j is strictly increasing, phi(j+1) = psi_j(chi_{j+1}(j+1)) > psi_j(j) = phi(j).
5. Tails of phi are subsequences of each psi_m. Fix m.
 a. For j >= m, phi(j) = psi_m(tau_j), with tau_m := m and tau_j := (chi_{m+1} o ... o chi_j)(j) for j > m.
 b. Each tau_j >= j, so tau_j -> infinity.
 c. Uniform convergence on a set is preserved under reindexing by any index sequence tending to infinity. Hence f_{phi(j)} -> g_m uniformly on B^m.
6. The limit function. For z in R^n pick an integer m >= |z|. Then z lies in B^m, and by step 5 the limit lim_j f_{phi(j)}(z) exists and equals g_m(z). Define V(z) to be this limit; it does not depend on m, by uniqueness of limits.
 a. V = g_m on B^m, so f_{phi(j)} -> V uniformly on every B^m.
 b. For real r choose an integer m >= r. Then Bbar_r(0) is contained in B^m (it is empty if r < 0), so f_{phi(j)} -> V uniformly on Bbar_r(0).
7. Properties of V.
 a. V(0) = lim f_{phi(j)}(0) = 0.
 b. Hoelder bound. Let z, z' be in R^n. Since phi(j) -> infinity and R_k -> infinity, for all large j we have R_{phi(j)} > max(|z|, |z'|), so ||f_{phi(j)}(z) - f_{phi(j)}(z')|| <= K |z - z'|^alpha. Letting j -> infinity, by pointwise convergence and continuity of the norm, ||V(z) - V(z')|| <= K |z - z'|^alpha.
 c. Continuity. Given z and epsilon > 0, choose eta > 0 with K eta^alpha < epsilon. Then |z' - z| < eta implies ||V(z') - V(z)|| <= K |z' - z|^alpha <= K eta^alpha < epsilon, using K >= 0 and alpha > 0. QED.

## Key steps

1. on Bbar_m(0) the tail k >= k_m is uniformly Hoelder and bounded by K m^alpha (f_k(0) = 0)
2. Arzela-Ascoli on the compact Bbar_m(0) with values in a compact ball of the finite-dimensional L gives a uniformly convergent subsequence of any subsequence
3. nested subsequences psi_m converge uniformly on Bbar_m(0); the diagonal phi(j) = psi_j(j) is strictly increasing
4. each tail of phi is a subsequence of psi_m, so f_{phi(j)} converges uniformly on every Bbar_m(0), hence on every Bbar_r(0)
5. the limit V satisfies V(0) = 0, the global Hoelder bound by passing to the limit, and is continuous

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `rg -l -i '\barzela|\bascoli\b|ArzelaAscoli' <snapshot>/mathlib/Mathlib <snapshot>/project`
- `rg -n -i 'blow-?up|arzela|ascoli|weak equation|weak solution' <snapshot>/project`
- `grep -n 'theorem hasFDerivAt_of_tendstoUniformlyOn|hasFDerivAt_of_tendstoUniformlyOnFilter|cauchy_map_of_uniformCauchySeqOn_fderiv' <snapshot>/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `grep (pinned Mathlib) for BoundedContinuousFunction.arzela_ascoli, ArzelaAscoli.isCompact_of_equicontinuous, tendsto_subseq_of_bounded, IsCompact.tendsto_subseq, TendstoUniformlyOn.tendsto_comp, setIntegral_eq_integral_of_forall_compl_eq_zero, norm_setIntegral_le_of_norm_le_const, integral_eq_sub_of_hasDerivAt, norm_integral_le_of_norm_le_const, opNorm_le_bound₂, le_opNorm₂, ContinuousOn.clm_apply, support_fderiv_subset, fderiv_const_smul, ContDiffOn.continuousOn_fderiv_of_isOpen, contDiff_one_iff_fderiv, continuousAt_rpow_const, rpow_inv_rpow, rpow_rpow_inv, tendsto_inv_nhdsGT_zero, tendsto_one_div_atTop_nhds_zero_nat, ball_subset_ball'`
- `python3 scan of dag.json: statuses of the sibling nodes (all 'decomposing'), lean_name collisions for dohr_eb_sch_bu_*, topic scan (arzela, ascoli, diagonal, uniform limit, weak limit), cross-branch dependency pattern`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') -> replayed child scope (open ...; namespace GMT.Ch05; namespace/end RectifiableVarifold; open RectifiableVarifold)`
- `lean -o build/GMT/Ch05/Submission.olean src/Submission.lean in scratch /tmp/blowup-decomp-*/ (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lean checks/Challenges.lean (first draft: TopologicalSpace/HSub/PseudoMetricSpace/AddCommGroup on the bilinear-form type fail at default depth), checks/Challenges2.lean (revised types elaborate)`
- `lean checks/node/Challenge_<key>.lean and checks/node/Solution_<key>.lean for the 5 keys (solutions against a scratch Submission declaring the children)`
- `lean checks/AsmLimit.lean (blowup_limit from the three leaf child types as axioms; #print axioms)`
- `lean checks/AsmParent.lean (frozen parent type from weak_eq_sub_affine, blowup_limit and the four sibling frozen types as axioms; #print axioms)`
- `lean checks/Inst.lean, checks/InstVerify.lean (instances: maxSynthPendingDepth 3 for Bil, smul/evaluation on L and L*, uniform structure on L, rpow, Haar volume)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Ascoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/UniformApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-22cb2001d8/parent-child-handoff.json`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean. Pinned Mathlib supplies the tools the children need: BoundedContinuousFunction.arzela_ascoli (Topology/ContinuousMap/Bounded/ArzelaAscoli.lean:109), ArzelaAscoli.isCompact_of_equicontinuous (Topology/UniformSpace/Ascoli.lean:499), hasFDerivAt_of_tendstoUniformlyOn (Analysis/Calculus/UniformLimitsDeriv.lean:419) and its Filter version (:308), tendsto_subseq_of_bounded (Topology/MetricSpace/Sequences.lean:38; not imported by the contract, so a child must add the import), TendstoUniformlyOn.tendsto_comp (UniformApproximation.lean:173), setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486), intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148), ContinuousLinearMap.opNorm_le_bound₂ and le_opNorm₂ (Operator/Bilinear.lean:67,71), ContinuousOn.clm_apply (BoundedLinearMaps.lean:476) and support_fderiv_subset (FDeriv/Const.lean:379). Neither Mathlib nor the project contains blow-up compactness, stability of weak equations or a C^1-limit lemma on growing domains. The project snapshot has no Arzela-Ascoli or weak-equation matches; the only blow-up hits are the Ch08 README varifold tangent cones, which are unrelated. dag.json: the four sibling prerequisites of this node are all still 'decomposing', so children cannot depend on them. There is no dohr_eb_sch_bu_* name, and no accepted node has an identical type. The closest node, dohr_eb_dql_c1Holder_of_tendstoUniformlyOn, is speculative-lean with a different type. Instance finding: at the default maxSynthPendingDepth, the frozen scope cannot synthesize TopologicalSpace, HSub, PseudoMetricSpace or AddCommGroup on the bilinear-form type, and inside proofs ContinuousSub on L* also fails. The child types therefore use joint continuity of (z,P,Q) -> b z P Q and scalar bounds. Inside proofs, set_option maxSynthPendingDepth 3 recovers these instances, and FiniteDimensional.proper_real gives ProperSpace. Lean checks: (1) all 5 child types elaborate as NodeChallenge targets, and every NodeSolution closes by exact Submission.X. (2) blowup_limit is proved without sorry from the three leaf types as axioms; #print axioms lists propext, Classical.choice, Quot.sound and those three. (3) The frozen parent type is proved without sorry from weak_eq_sub_affine, blowup_limit and the four sibling types as axioms; #print axioms lists exactly these six and the three standard axioms. (4) Instances of the inline constructions check out: (s • T) Q = s * T Q on L*; (s • P) v = s • P v on L; B (s • P) Q = s * B P Q; TendstoUniformlyOn on L is the operator-norm metric version; ‖z‖ ^ α is Real.rpow; volume on Rn n is an additive Haar measure.
