# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.cancel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 8 (“a + b ≤ λ(s + e + e + b) = λ(s + 2e) + λb. Since λ ≥ 1, λb = b + (λ − 1)b in [0, ∞], and b < ∞ can be cancelled: a ≤ λ(s + 2e) + (λ − 1)b ≤ λ(s + 2e) + (λ − 1)M_{B_{G₃}}(T). Finally λ − 1 = ofReal(Lⁿ) − ofReal(1) = ofReal(Lⁿ − 1)”), stated abstractly. No siblings are used.
1. b ≠ ∞, since b ≤ M and M ≠ ∞.
2. L ≥ 1 gives Lⁿ ≥ 1 (one_le_pow₀), so Lⁿ − 1 ≥ 0. Write Lⁿ = 1 + (Lⁿ − 1) with both summands ≥ 0. ENNReal.ofReal_add then gives λ := ofReal(Lⁿ) = ofReal(1) + ofReal(Lⁿ − 1) = 1 + κ, where κ := ofReal(Lⁿ − 1).
3. In the commutative semiring [0, ∞], s + e + e + b = (s + 2e) + b. Hence λ(s + e + e + b) = λ(s + 2e) + λb = λ(s + 2e) + (1 + κ)b = (λ(s + 2e) + κb) + b.
4. So the hypothesis reads a + b ≤ (λ(s + 2e) + κb) + b. As b ≠ ∞ (step 1), b can be cancelled on the right (ENNReal.le_of_add_le_add_right): a ≤ λ(s + 2e) + κb.
5. Since b ≤ M, and multiplication and addition are monotone in [0, ∞], κb ≤ κM. Hence a ≤ λ(s + 2e) + κM = ofReal(Lⁿ)·(s + 2e) + ofReal(Lⁿ − 1)·M. ∎

## Key steps

1. b ≤ M < ∞, and ofReal(Lⁿ) = 1 + ofReal(Lⁿ − 1) because Lⁿ ≥ 1.
2. The right side equals (ofReal(Lⁿ)(s + 2e) + ofReal(Lⁿ − 1)b) + b; cancel the finite b.
3. Replace b by M using b ≤ M.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD (b4d606d), mathlib 25730c7c, simongmt 2b366308; cmp local-references/.../project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `python3 over RUN/dag.json: status, lean_name and lean_statement of the selected node, its parent local_comparison-a1, the sibling retraction_comparison and the seven resolved dependencies`
- `python3 over RUN/dag.json: accepted nodes with candidate_commit whose lean_statement mentions massOn, support, restrictDomain, IsIntegerMultiplicity or Disjoint (found rsd_cmr_support_subset_of_vanish, regcomp_integer_multiplicity_sub, rsd_isIntegerMultiplicity_int_combination, dtc_massOn_eq_of_agreeOn, cmc_ml_massOn_eq_of_disjoint_sub_support, dtc_bc_lc_measure_le_add); regex search for zero-mass lemmas (only dtc_dim_zero_eq_zero); collision scan for dimred_mbl_lc_ic_* (no match)`
- `python3 over nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-comparison-a1/decomposition-v1.json (texts of reused children) and nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `grep -n 'def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|massAdmissibleOn|le_massOn|massOn_mono|def GeometricCurrentOn.support|zeroRegion|def testFormOnInclusion|restrictDomain_apply|boundary_apply|zero_apply' in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality}.lean`
- `grep -rn 'theorem mul_le_mul_right|protected theorem le_of_add_le_add_right|lemma one_le_pow₀' in local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n '_existing_lean_name_problem|_overlay_accepted_children|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; contract_scope/child_modules in verifier/gmt-compare.py`
- `sed -n 150,275p book/chapter-07.txt (Simon 7.2.4, Remark 7.2.5(2), (8)–(12) at lines 223–260)`
- `lake env lean /tmp/ic_dec/Types.lean (all child and dependency types as _root_ theorems after import GMT.Ch07.Submission in the replayed contract scope); lake env lean /tmp/ic_dec/Proofs.lean (conditional proofs n1–n5_check and assembly_check, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-32e3afa931/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-32e3afa931/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/ic_dec/Types.lean`
- `/tmp/ic_dec/Proofs.lean`

The pins match the manifest: project b4d606d, Mathlib 25730c7c, SimonGMT 2b366308. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical. Neither the pinned libraries nor the accepted DAG nodes contain the cycle construction, the T + Y|_U construction, the three-region estimate or the [0, ∞] cancellation. These four are new, as is the zero-mass lemma: the only accepted zero-mass statement is dtc_dim_zero_eq_zero, for 0-dimensional minimizers. Six accepted declarations are reused with byte-identical types: dtc_vanish_off_support, dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity, lcmp_measure_le_add_of_open_nhds (already prerequisites of this node) and rsd_cmr_support_subset_of_vanish (= (p2)). SimonGMT provides massOn/le_massOn/massOn_mono, support/zeroRegion/isOpen_zeroRegion, restrictDomain_apply, testFormOnInclusion_coe and boundary_apply/zero_apply. Mathlib provides ENNReal.le_of_add_le_add_right, ENNReal.ofReal_add(_le), one_le_pow₀ and measure_union. Lean checks: all child types elaborate in the comparator scope. Each new child is proved from its declared siblings. The exact frozen parent type is proved from the five new child types and the frozen type of retraction_comparison. Only propext, Classical.choice and Quot.sound are used. The names dimred_mbl_lc_ic_* are unused in the DAG and the project.
