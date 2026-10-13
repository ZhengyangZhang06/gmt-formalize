# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.total_bounded-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.total_bounded-a1.mass_sub-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (F1) of the parent proof, i.e. the triangle inequality for Simon's mass 6.2.5 (M_G is a supremum over admissible forms), as used in Simon's proof of Theorem 6.7.2.
1. By definition M_G(A − B) = sup{ofReal((A − B)(ω)) : ω admissible for M_G}. By the least-upper-bound property (sSup_le) it suffices to fix an admissible ω and prove ofReal((A − B)(ω)) ≤ M_G(A) + M_G(B).
2. −ω is admissible for M_G. Indeed 𝒟ⁿ(U) is a submodule, so −ω ∈ 𝒟ⁿ(U), and its underlying form is the pointwise negative of the underlying form of ω. Hence tsupport(−ω) = tsupport(ω) ⊆ G (tsupport_neg), and for every x, |(−ω)(x)| = |−(ω(x))| = |ω(x)| ≤ 1, because the Euclidean coefficient norm is invariant under negation (covectorEuclideanNorm_neg).
3. (A − B)(ω) = A(ω) − B(ω) by the definition of the contract instance Sub, and B(−ω) = −B(ω) because the underlying functional of B is linear. Hence (A − B)(ω) = A(ω) + B(−ω).
4. For real s, t one has ofReal(s + t) ≤ ofReal(s) + ofReal(t) (ENNReal.ofReal_add_le). With step 3, ofReal((A − B)(ω)) ≤ ofReal(A(ω)) + ofReal(B(−ω)).
5. Every admissible value is bounded by the corresponding mass (GeometricCurrentOn.le_massOn): ofReal(A(ω)) ≤ M_G(A) because ω is admissible, and ofReal(B(−ω)) ≤ M_G(B) because −ω is admissible by step 2. Adding these two bounds to step 4 gives ofReal((A − B)(ω)) ≤ M_G(A) + M_G(B); by step 1, M_G(A − B) ≤ M_G(A) + M_G(B). ∎

## Key steps

1. Reduce to one admissible ω, since M_G(A − B) is a supremum over admissible forms.
2. −ω is admissible: the same topological support and a negation-invariant Euclidean coefficient norm.
3. (A − B)(ω) = A(ω) + B(−ω), and ofReal is subadditive.
4. Bound ofReal(A(ω)) by M_G(A) and ofReal(B(−ω)) by M_G(B).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n "massOn_sub|massOn_add|mass_sub|restrictDomain|cmc_fc_|IsIntegerMultiplicity \(.* - " project/GMT --glob '*.lean' (only the contract's blowUp uses restrictDomain)`
- `rg -n "massOn|mass " project/GMT/Ch06/Contract.lean (no subadditivity or restriction lemma)`
- `rg -n "theorem exists_nnreal_pos_mul_lt|theorem ofReal_add_le|theorem tsupport_neg|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem Finite.image" mathlib/Mathlib --glob '*.lean'`
- `rg -n "tsupport_neg\b" mathlib/Mathlib --glob '*.lean'; rg -n "theorem mulTSupport_inv" mathlib/Mathlib --glob '*.lean'; rg -n "^theorem restrict_restrict \(|^theorem setIntegral_eq_integral_of_forall_compl_eq_zero" mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn "massOn_sub\|massOn_add\|mass_add\|mass_sub\|massOn_neg\|restrictDomain.*mass\|mass.*restrictDomain\|massOn_le_add\|massOn_triangle" lake-packages-25730c7c/simongmt --include=*.lean (no match)`
- `grep -n '^def \|^theorem \|^lemma \|^structure \|^instance ' simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality}.lean; grep -n 'def HasApproximateTangentSpaceAt\|def blowUpMap\|theorem CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 scan of dag.json: accepted lean_statements mentioning restrictDomain or massOn; mass triangle-inequality statements (only lcmp_massOn_le_add_of_eval_eq, decomposing, other parent); exact lean_statement/status/candidate_commit of dtc_restrictDomain_isIntegerMultiplicity and dtc_massOn_eq_of_agreeOn; sibling statuses under root.compactness_of_minimizing_currents-a1.flat_convergence-a1; occurrences of cmc_fc_tb_massOn_sub_le (none)`
- `git show 8f3bacb2e7f68423e88b488e5939a0d419c646fb:GMT/Ch07/Submission.lean; git show 0c79e2ab8192c141221cbe30fcd242e4becc6f00:GMT/Ch07/Submission.lean; git log --all --oneline -S cmc_fc_tb_ (no match)`
- `sed -n 2004,2140p book/chapter-06.txt (Simon Ch. 6, 7.1-7.2)`
- `grep -n 'def _existing_lean_name_problem|def _solve_children|def _overlay_accepted_children|def _install_parent_supplied_child_handoff|def _accepted_checkpoint' runtime.py; grep -n 'def ensure' store.py`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the three child types`
- `lake env lean /tmp/tbdec-claude/Types.lean; lake env lean /tmp/tbdec-claude/Child.lean (#print axioms check_massOn_sub_le); lake env lean /tmp/tbdec-claude/Assembly.lean (#print axioms tb_assembly)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-total-bounded-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-total-bounded-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-total-bounded-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-restrict-im-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-mass-agree-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tbdec-claude/Types.lean`
- `/tmp/tbdec-claude/Child.lean`
- `/tmp/tbdec-claude/Assembly.lean`

The snapshot (project b4d606db, mathlib 25730c7c) Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot project nor the pinned SimonGMT Chapter06 has a mass-subadditivity, restriction-mass or restriction-IM lemma; SimonGMT provides only massOn_mono, le_massOn, restrictDomain_apply, testFormOnInclusion_coe and GeometricCurrentOn.ext. The pinned Mathlib supplies the tools the child proofs and the assembly cite: ENNReal.ofReal_add_le, tsupport_neg (to_additive of mulTSupport_inv), setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, Measure.restrict_restrict, setIntegral_eq_integral_of_forall_compl_eq_zero, Set.Finite.image and ENNReal.exists_nnreal_pos_mul_lt. Two accepted DAG declarations are reused with byte-identical frozen types and self-contained candidate commits: dtc_restrictDomain_isIntegerMultiplicity and dtc_massOn_eq_of_agreeOn. The new name cmc_fc_tb_massOn_sub_le is unused. The three child types elaborate and pass validate_lean_statement. The new child's proof compiles. The conditional assembly of the exact selected type from the children and the sibling cmc_fc_extend_to_univ compiles with only propext, Classical.choice and Quot.sound.
