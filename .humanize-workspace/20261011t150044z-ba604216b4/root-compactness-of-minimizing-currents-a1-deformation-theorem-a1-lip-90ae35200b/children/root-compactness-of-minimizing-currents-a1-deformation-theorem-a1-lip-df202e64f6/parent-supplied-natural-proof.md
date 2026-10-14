# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1.mass_support_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 3–6 (A0: representation of finite-mass currents via (REP) and (VO)). This is Simon Ch. 6, 2.7–2.8 with 2.12 (spt T = spt μ_T), book/chapter-06.txt lines 265–307. Conventions (SimonGMT Chapter06 and the frozen contract): |α| := covectorEuclideanNorm α, the Euclidean norm of the values α(e_{I 1}, …, e_{I k}) over strictly increasing I. For X ∈ 𝒟_k(univ) = GeometricCurrentOn univ k and any W, M_W(X) := X.massOn W = sSup {ENNReal.ofReal (X ω) : ω ∈ massAdmissibleOn univ k W}, where ω ∈ massAdmissibleOn univ k W means tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. M(X) := X.mass, which is by definition X.massOn univ. X.zeroRegion is the union of the open W with compact closure (closure W ⊆ univ) on which X vanishes; this set is open (GeometricCurrentOn.isOpen_zeroRegion), and spt X := X.support = univ \ X.zeroRegion.
1. Fix N, k, X, ψ, c with X.mass < ∞ and |ψ(x)| ≤ c for all x ∈ spt X. For every W ⊆ ℝ^N, X.massOn W ≤ X.massOn univ = X.mass < ∞ (GeometricCurrentOn.massOn_mono, since W ⊆ univ). So the finiteness hypothesis of (REP) holds for P := N, n := k, U := univ (isOpen_univ); its CompactlyContained premise is not even needed.
2. Apply (REP) to X. Only three of its conclusions are used. (a) X.massOn W = μ W for every open W. (b) |ξ x α| ≤ |α| for all x and α. (c) X ω = ∫ ξ x (ω x) dμ for every ω ∈ 𝒟^k(univ).
3. Total mass. By (a) with W := univ (open), μ univ = X.massOn univ = X.mass < ∞. So μ is a finite measure (IsFiniteMeasure μ), and μ.real univ = (μ univ).toReal = X.mass.toReal (measureReal_def).
4. Concentration. Z := X.zeroRegion is open, so (a) gives μ Z = X.massOn Z. Let ω ∈ massAdmissibleOn univ k Z, so tsupport ω ⊆ Z. Since spt X = univ \ Z, tsupport ω is disjoint from spt X. (VO) with P := N, n := k, U := univ, S := X then gives X ω = 0, hence ENNReal.ofReal (X ω) = 0. Every element of the set whose supremum defines X.massOn Z is therefore ≤ 0, so X.massOn Z ≤ 0 (sSup_le), i.e. X.massOn Z = 0 (an empty set also has supremum 0). Hence μ Z = 0.
5. The set {x | x ∉ spt X} = {x | x ∉ univ \ Z} is contained in Z, which is μ-null. Hence μ-a.e. x lies in spt X (ae_iff, measure_mono_null).
6. For μ-a.e. x, namely every x ∈ spt X: ‖ξ x (ψ x)‖ = |ξ x (ψ x)| ≤ |ψ(x)| ≤ c, by (b) with α := ψ(x) and the hypothesis on ψ.
7. μ is finite and ‖ξ x (ψ x)‖ ≤ c μ-a.e. So norm_integral_le_of_norm_le_const gives ‖∫ ξ x (ψ x) dμ‖ ≤ c · μ.real univ. This lemma needs neither integrability nor a sign condition on c, so c < 0 needs no separate treatment.
8. By (c) with ω := ψ, X ψ = ∫ ξ x (ψ x) dμ. By steps 7 and 3, |X ψ| = ‖∫ ξ x (ψ x) dμ‖ ≤ c · μ.real univ = c · X.mass.toReal. □

## Key steps

1. massOn_mono gives X.massOn W ≤ X.mass < ∞ for every W, so (REP) applies with U := univ and yields μ, ξ.
2. (REP)(a) with W := univ gives μ univ = X.mass < ∞, so μ is finite and μ.real univ = X.mass.toReal.
3. Z := X.zeroRegion is open. Each test form admissible for X.massOn Z has tsupport disjoint from spt X, so (VO) gives X.massOn Z = 0 and hence μ Z = 0.
4. So μ-a.e. x lies in spt X, where |ξ x (ψ x)| ≤ |ψ x| ≤ c.
5. norm_integral_le_of_norm_le_const and (REP)(c) give |X ψ| ≤ c · μ.real univ = c · X.mass.toReal.

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
