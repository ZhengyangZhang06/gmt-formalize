# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.cycle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (“X := S − C is integer multiplicity ((IMC)(c)), ∂X = ∂S − ∂C = 0 (p6) and spt X ⊆ W. Y := X − (0 − Ŷ) (= X + Ŷ) is integer multiplicity (p3) and ∂Y = ∂X + ∂Ŷ = 0 (p6). If tsupport ω ∩ F = ∅, then X(ω) = 0 and Ŷ(ω) = 0 by (VO) …, so Y(ω) = 0; by (p2) spt Y ⊆ F, so spt Y is compact”). Three changes: the parent's spt(S − C) ⊆ W ⊆ F is used only as spt(S − C) ⊆ F; (p3) is realized with 0 = Ŷ − Ŷ; and (p2) is supplied by support_of_vanishing. Siblings used: (VO) vanish_off_support; (IMC) im_calculus, part (c): if A, B ∈ 𝒟_k(V) are integer multiplicity and V is open, then so is A − B; (SV) support_of_vanishing.
Conventions: all currents live in the open set ℝ^P (= univ). For currents A, B, (A − B)(ω) = A(ω) − B(ω), and 0 is the zero current. For A ∈ 𝒟_{m+1}(ℝ^P) and η ∈ 𝒟^m(ℝ^P), ∂A(η) = A(dη), where dη ∈ 𝒟^{m+1}(ℝ^P) is the exterior derivative of η (GeometricCurrentOn.boundary_apply, exteriorDerivativeTestOn).
1. (Integer multiplicity.) Apply (IMC)(c) in the open set ℝ^P four times. X := S − C is integer multiplicity, because C and S are. D := Ŷ − Ŷ is integer multiplicity. N := D − Ŷ is integer multiplicity. Finally Y := X − N is integer multiplicity.
2. (Values.) For every ω ∈ 𝒟^{m+1}(ℝ^P), Y(ω) = X(ω) − ((Ŷ(ω) − Ŷ(ω)) − Ŷ(ω)) = X(ω) + Ŷ(ω) = (S − C)(ω) + Ŷ(ω).
3. (Boundary.) Let η ∈ 𝒟^m(ℝ^P) and ζ := dη. Evaluating ∂S = ∂C at η gives S(ζ) = C(ζ), and evaluating ∂Ŷ = 0 at η gives Ŷ(ζ) = 0. Hence ∂Y(η) = Y(ζ) = (S(ζ) − C(ζ)) − ((Ŷ(ζ) − Ŷ(ζ)) − Ŷ(ζ)) = 0 − (0 − 0) = 0 = 0(η). Since η is arbitrary, ∂Y = 0 by extensionality of currents (GeometricCurrentOn.ext).
4. (Vanishing away from F.) Let ω ∈ 𝒟^{m+1}(ℝ^P) with tsupport ω ∩ F = ∅. Since spt X = spt(S − C) ⊆ F and spt Ŷ ⊆ F, tsupport ω is disjoint from spt X and from spt Ŷ. So (VO) gives X(ω) = 0 and Ŷ(ω) = 0, and step 2 gives Y(ω) = 0.
5. (Support.) Apply (SV) with the open set ℝ^P, the compact set K := F ⊆ ℝ^P and the current Y; step 4 is its hypothesis. It gives spt Y ⊆ F, and spt Y is compact.
6. By steps 1–5, Y has all the required properties. ∎

## Key steps

1. Y := (S − C) − ((Ŷ − Ŷ) − Ŷ) is integer multiplicity by im_calculus (c), and Y(ω) = (S − C)(ω) + Ŷ(ω).
2. ∂Y(η) = S(dη) − C(dη) + Ŷ(dη) = 0, because ∂S = ∂C and ∂Ŷ = 0.
3. Y vanishes on forms supported away from F (vanish_off_support), so support_of_vanishing gives spt Y ⊆ F with spt Y compact.

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
