# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1.bounded_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 7–10 (0(b): bounded linear functionals are currents with mass ≤ C). This is Simon Ch. 6, Definition 2.1 with the test-form topology of §1 and the mass 2.4, book/chapter-06.txt lines 170–176 (topology of 𝒟ⁿ(U)), 192–194 (Definition 2.1) and 220–226 (2.4). Conventions. A GeometricCurrentOn univ k is a pair: a linear functional toCurrent on TestFormOn univ k, and continuity' — toCurrent (ω_j) → 0 whenever TestFormOnConverges ω_j 0. TestFormOnConverges ω_j 0 means: there is a compact K ⊆ univ with tsupport ω_j ⊆ K for all j and tsupport 0 ⊆ K, and for every m, iteratedFDeriv ℝ m ω_j → iteratedFDeriv ℝ m 0 uniformly on K. |α| := covectorEuclideanNorm α = √(Σ_{I : Fin k → Fin N} (if StrictMono I then α(e_{I 1}, …, e_{I k})² else 0)), where e_i = EuclideanSpace.basisFun (Fin N) ℝ i = EuclideanSpace.single i 1. ‖α‖ is the operator norm of the continuous alternating map α. T.mass = T.massOn univ = sSup {ENNReal.ofReal (T ω) : ω ∈ massAdmissibleOn univ k univ}, and ω ∈ massAdmissibleOn univ k univ means tsupport ω ⊆ univ and |ω(x)| ≤ 1 for all x.
1. Coefficient bound. Let A := √(N^k) ≥ 0. Then |α| ≤ A·‖α‖ for every k-covector α on ℝ^N. Fix I : Fin k → Fin N. ContinuousAlternatingMap.le_opNorm gives |α(e_{I 1}, …, e_{I k})| ≤ ‖α‖·∏_i ‖e_{I i}‖ = ‖α‖, since ‖EuclideanSpace.single i 1‖ = 1. So the I-th summand is ≤ ‖α‖² (if StrictMono I it is the square of a number of absolute value ≤ ‖α‖; otherwise it is 0 ≤ ‖α‖²). There are Fintype.card (Fin k → Fin N) = N^k summands (Fintype.card_fun, Fintype.card_fin). So the sum is ≤ N^k·‖α‖², and |α| ≤ √(N^k·‖α‖²) = √(N^k)·‖α‖ (Real.sqrt_le_sqrt, Real.sqrt_mul, Real.sqrt_sq).
2. Sign of C. Apply the hypothesis to ω := 0 and c := 1. Then |0(x)| = covectorEuclideanNorm 0 = 0 ≤ 1 for all x, so 0 = |T₀ 0| ≤ C·1, i.e. 0 ≤ C.
3. Continuity. Let (ω_j) satisfy TestFormOnConverges ω_j 0, with compact K as in the conventions. Use only the m = 0 part. We have ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ (norm_iteratedFDeriv_zero) and iteratedFDeriv ℝ 0 0 x = 0 (its norm is ‖0 x‖ = 0). Metric.tendstoUniformlyOn_iff then gives: for every δ > 0 there is j₀ with ‖ω_j(x)‖ < δ for all j ≥ j₀ and x ∈ K. If x ∉ K then x ∉ tsupport ω_j, so ω_j(x) = 0 (image_eq_zero_of_notMem_tsupport). Hence for j ≥ j₀, ‖ω_j(x)‖ ≤ δ for every x ∈ ℝ^N, and by step 1, |ω_j(x)| ≤ A·δ for every x. The hypothesis with c := A·δ gives |T₀(ω_j)| ≤ C·(A·δ) for all j ≥ j₀. Now let ε > 0 and put δ := ε/(C·A + 1), which is > 0 because C·A + 1 ≥ 1 by step 2 and A ≥ 0. Then C·A·δ = C·A·ε/(C·A + 1) < ε, so |T₀(ω_j) − 0| < ε for all j ≥ j₀. Hence T₀(ω_j) → 0 (Metric.tendsto_atTop).
4. Definition of T. T := ⟨T₀, step 3⟩ is a GeometricCurrentOn univ k, and T(ω) = T₀(ω) for every ω by definition.
5. Mass. Let ω ∈ massAdmissibleOn univ k univ. Then |ω(x)| ≤ 1 for all x, so the hypothesis with c := 1 gives T(ω) = T₀(ω) ≤ |T₀(ω)| ≤ C·1 = C. Hence ENNReal.ofReal (T ω) ≤ ENNReal.ofReal C (ENNReal.ofReal_le_ofReal). Taking the supremum (sSup_le), T.mass = T.massOn univ ≤ ENNReal.ofReal C. □

## Key steps

1. |α| ≤ √(N^k)·‖α‖: each coordinate value is bounded by ‖α‖ (le_opNorm, unit basis vectors), and there are N^k summands.
2. ω := 0, c := 1 in the hypothesis gives 0 ≤ C.
3. TestFormOnConverges ω_j 0 gives sup_x ‖ω_j(x)‖ → 0 (the m = 0 derivative converges uniformly on K, and ω_j = 0 off K), so |T₀(ω_j)| ≤ C·√(N^k)·δ eventually, i.e. T₀(ω_j) → 0.
4. T := ⟨T₀, continuity⟩ satisfies T ω = T₀ ω, and admissible forms give T ω ≤ |T₀ ω| ≤ C, so T.mass ≤ ofReal C by sSup_le.

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
