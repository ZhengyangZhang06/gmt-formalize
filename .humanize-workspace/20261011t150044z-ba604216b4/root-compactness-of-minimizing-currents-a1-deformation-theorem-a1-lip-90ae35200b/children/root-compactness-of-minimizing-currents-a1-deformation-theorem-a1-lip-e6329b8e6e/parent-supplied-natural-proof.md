# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1.locality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2 (0(c), (S3)). Simon Ch. 6, 2.11, book/chapter-06.txt lines 296–303: a current vanishes on test forms supported away from its support.
1. Let ψ := η − η' ∈ 𝒟^k(univ), the difference in the submodule TestFormOn univ k. Its underlying form is x ↦ η(x) − η'(x) (Submodule.coe_sub, Pi.sub_apply).
2. For x ∈ W, ψ(x) = η(x) − η'(x) = 0 by hypothesis. So support ψ = {x | ψ(x) ≠ 0} ⊆ Wᶜ. Since W is open, Wᶜ is closed, so tsupport ψ = closure (support ψ) ⊆ Wᶜ (closure_minimal, IsOpen.isClosed_compl).
3. tsupport ψ ⊆ Wᶜ and spt X ⊆ W, and Wᶜ is disjoint from W. So tsupport ψ is disjoint from spt X (Set.disjoint_of_subset with disjoint_compl_left).
4. Apply (VO) with P := N, n := k, U := univ, S := X, ω := ψ: X(ψ) = 0.
5. X acts through the linear map X.toCurrent, so X(ψ) = X(η) − X(η') (LinearMap.map_sub). Hence X(η) − X(η') = 0, i.e. X(η) = X(η'). □

## Key steps

1. ψ := η − η' vanishes on the open set W, so tsupport ψ ⊆ Wᶜ (Wᶜ is closed).
2. spt X ⊆ W, so tsupport ψ is disjoint from spt X.
3. (VO) gives X(ψ) = 0, and linearity gives X(η) = X(η').

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, as in manifest.json)`
- `rg -n cmcdt_lpo_tk local-references/123e8435b4a2469b/project/GMT (no match)`
- `python3 scan of dag.json: 2112 lean_name fields for cmcdt_lpo_tk / tk_ (no match); exact lean_statement equality of each child type against all nodes (no match); selected node depth 5, depends_on []`
- `rg -n 'theorem norm_integral_le_of_norm_le_const' mathlib/Mathlib/MeasureTheory/Integral/Bochner/ (Basic.lean:1004)`
- `rg -n 'theorem norm_iteratedFDeriv_zero|theorem iteratedFDeriv_zero_apply' mathlib/Mathlib/Analysis/Calculus/ContDiff/ (FTaylorSeries.lean:814, :823)`
- `rg -n image_eq_one_of_notMem_mulTSupport mathlib/Mathlib/Topology/Algebra/Support.lean (:111, additive form image_eq_zero_of_notMem_tsupport)`
- `rg -n 'theorem tendstoUniformlyOn_iff' mathlib/Mathlib/Topology/MetricSpace/ (Pseudo/Basic.lean:142)`
- `rg -n 'theorem le_opNorm' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean (:212)`
- `rg -n 'theorem measureReal_def' mathlib/Mathlib/MeasureTheory/Measure/ (MeasureSpaceDef.lean:105)`
- `rg -n 'theorem basisFun_apply' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (:806); rg -n card_fun mathlib/Mathlib/Data/Fintype/BigOperators.lean (:199)`
- `grep -n of SimonGMT Chapter06: Currents.lean (TestFormOnConverges :132, GeometricCurrentOn :145, tsupport_exteriorDerivative_subset :182, boundary :325, boundary_apply :333), Mass.lean (covectorEuclideanNorm :30, massAdmissibleOn :57, massOn :68, mass :74, massOn_mono :81), CurrentLocalEquality.lean (VanishesOn :101, zeroRegion :108, support :115, isOpen_zeroRegion :119)`
- `sed -n 160,310p book/chapter-06.txt (Simon 6.1 test-form topology, 6.2.1-2.12)`
- `grep -n max_depth /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py (:1382 node.depth >= max_depth stops splitting); sed -n 1,200p leaf_verification.py (machine leaf appends one theorem; forbidden-token regex)`
- `lake env lean /tmp/tk-decomp-q8v3/Types.lean (#check availability of cited lemmas in the frozen import closure)`
- `lake env lean /tmp/tk-decomp-q8v3/TypesOnly.lean (four child types elaborate; sorry-free conditional assembly of the exact parent type; #print axioms)`
- `lake env lean /tmp/tk-decomp-q8v3/FromPayload.lean (sorry-free single-theorem proofs of all four children from the payload strings, plus assembled cmcdt_lpo_current_toolkit; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-90ae35200b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-3968ae1944/decomposition-v1.json`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/leaf_verification.py`
- `/tmp/tk-decomp-q8v3/Types.lean`
- `/tmp/tk-decomp-q8v3/TypesOnly.lean`
- `/tmp/tk-decomp-q8v3/FromPayload.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Submission.lean. There are no cmcdt_lpo_tk_* declarations in the snapshot or the DAG, and no node has any of the four child types, so nothing is reused and the names are fresh. Every library fact the child proofs cite is in the frozen import closure of GMT.Ch07.Submission: norm_integral_le_of_norm_le_const, norm_iteratedFDeriv_zero, image_eq_zero_of_notMem_tsupport, Metric.tendstoUniformlyOn_iff, ContinuousAlternatingMap.le_opNorm, measureReal_def, EuclideanSpace.basisFun_apply and Fintype.card_fun, plus SimonGMT's massOn_mono, isOpen_zeroRegion, boundary_apply and tsupport_exteriorDerivative_subset. The four child types elaborate, and a conditional assembly proves the exact frozen parent type from them without sorry. Each child also has a complete single-theorem proof with no helper declarations, compiled from the payload strings. Only propext, Classical.choice and Quot.sound are used. Simon 6.2.1-2.12 (book/chapter-06.txt lines 170-307) matches the four children.
