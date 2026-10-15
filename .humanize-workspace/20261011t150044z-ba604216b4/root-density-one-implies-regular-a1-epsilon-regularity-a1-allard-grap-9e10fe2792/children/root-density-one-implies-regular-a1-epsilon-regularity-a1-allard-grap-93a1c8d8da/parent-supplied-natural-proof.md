# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1.tangent_dimension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the structural fact used in Step 5 of the parent proof: 'μ-a.e. x is a point where M has an n-dimensional approximate tangent plane T_xM = approxTangentPlane n M x'. It comes from IMRep.orients and the definition of approxTangentPlane (Simon Ch. 6, Definition 3.1; Ch. 3, Definition 1.4).
Notation: M := R.carrier, ν := Hⁿ⌞M = μHE[n].restrict M, μ_R := R.measure.

1. The dimension is part of the tangent predicate. In SimonGMT Chapter03, HasApproximateTangentSpaceAt n M x Q is defined as the conjunction of Module.finrank ℝ Q = n with the blow-up convergence condition of Simon Ch. 3, 1.4. Its first component is the accessor HasApproximateTangentSpaceAt.finrank_eq.

2. Pointwise consequence. Fix x such that some subspace Q satisfies HasApproximateTangentSpaceAt n M x Q, and let h denote the statement ∃ Q, HasApproximateTangentSpaceAt n M x Q.
(a) In the frozen contract, approxTangentPlane n M x is the dependent if-then-else 'if h : ∃ Q, HasApproximateTangentSpaceAt n M x Q then h.choose else ⊥'.
(b) Since h holds, approxTangentPlane n M x = h.choose (dite_eq_left, formerly dif_pos).
(c) h.choose satisfies HasApproximateTangentSpaceAt n M x h.choose (Exists.choose_spec).
(d) By Step 1, Module.finrank ℝ (approxTangentPlane n M x) = n.

3. Existence ν-a.e. The field R.orients of the triple states: for ν-almost every x there is Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (R.orient x) Q. Discarding the second conjunct, the property E(x) :≡ (∃ Q, HasApproximateTangentSpaceAt n M x Q) holds for ν-a.e. x.

4. Transfer to μ_R. μ_R = ν.withDensity (x ↦ θ(x)) is absolutely continuous with respect to ν (Mathlib withDensity_absolutelyContinuous), so every ν-null set is μ_R-null. Applied to the ν-null set {x : ¬E(x)} (Measure.AbsolutelyContinuous.ae_le), this shows that E(x) holds for μ_R-a.e. x.

5. Conclusion. By Step 2, Module.finrank ℝ (approxTangentPlane n M x) = n at every x with E(x). By Step 4 this holds for μ_R-almost every x. ∎

## Key steps

1. HasApproximateTangentSpaceAt n M x Q contains finrank Q = n as its first conjunct (HasApproximateTangentSpaceAt.finrank_eq).
2. If some approximate tangent space exists at x, approxTangentPlane n M x is the chosen one (dite_eq_left/dif_pos, Exists.choose_spec), so it has dimension n.
3. R.orients gives existence for Hⁿ⌞M-a.e. x; since R.measure = (Hⁿ⌞M).withDensity θ ≪ Hⁿ⌞M, it holds R.measure-a.e.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (identical)`
- `sed -n 1,200p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean  (HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.finrank_eq)`
- `rg -n 'theorem (exists_maximal|.*[Ss]eparated.*maximal|.*maximal.*[Ss]eparated)' mathlib/Mathlib; rg -n 'IsSeparated' mathlib/Mathlib/Topology/MetricSpace; sed -n 1,140p mathlib/Mathlib/Topology/MetricSpace/Cover.lean; sed -n 250,340p mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `rg -n "theorem measure_biUnion_finset|theorem measure_compl_support|theorem withDensity_absolutelyContinuous|theorem meas_ge_le_lintegral_div|theorem mul_meas_ge_le_lintegral₀|theorem lintegral_finset_sum'|theorem setLIntegral_const|theorem lintegral_mono_set|theorem lintegral_const_mul'|theorem exists_nat_mul_gt" mathlib/Mathlib`
- `rg -n 'lintegral_finset_sum|theorem measure_compl_support|lemma measure_compl_support|support_mem_ae|nonempty_inter_support_of_pos' mathlib/Mathlib`
- `rg -n 'theorem (norm_starProjection|starProjection_orthogonal|sub_starProjection|starProjection_add|norm_sub_starProjection|starProjection_apply|starProjection_orthogonal_val)' mathlib/Mathlib/Analysis/InnerProductSpace; sed -n 195,230p and 405,416p and 585,600p mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n 'theorem .*clm_apply|lemma .*clm_apply|apply_continuousLinearMap|theorem .*comp_aestronglyMeasurable₂|aestronglyMeasurable_comp₂' mathlib/Mathlib/MeasureTheory  (no AEStronglyMeasurable.clm_apply; ContinuousLinearMap.aestronglyMeasurable_comp₂ exists)`
- `python3 -I scan of dag.json lean_statements and nodes/*/decomposition-v*.json for a.e. statements mentioning finrank and approxTangentPlane  (only the frozen parent-level dorag_* statements; nothing reusable)`
- `ls .humanize/math-wiki; rg -l finrank .humanize/math-wiki; rg -n 'maximal.*separated|packing|Chebyshev|Markov' .humanize/math-wiki  (no matching accepted lemma)`
- `grep -l dorag_aa_ */.humanize/github-theorem-prover/runs/*/dag.json; grep -rl --include=*.json dorag_aa_ */.humanize/github-theorem-prover/runs/*/nodes; git grep -c dorag_aa_ $(git for-each-ref) -- 'GMT/*.lean'  (no hits in 8 DAGs, node JSONs, 487 refs)`
- `awk 'NR>=292 && NR<=375' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt  (Simon Lemma 2.5 and proof)`
- `python3 /tmp/affapprox-decomp/scripts/mkchal.py  (verifier gmt-compare.py child_modules, contract scope) then lean on /tmp/affapprox-decomp/challenges/Challenge_{separated_net,tangent_dimension,low_height_point,height_bounds,PARENT}.lean  (all exit 0, only 'declaration uses sorry')`
- `python3 -I lean_contract.validate_lean_statement on the four child lean_statements  (all accepted unchanged)`
- `lean /tmp/affapprox-decomp/work/AllChecks.lean  (0 errors; #print axioms Kid.separated_net, Kid.tangent_dimension, Kid.low_height_point, Kid.height_bounds, AffAsm.assembly, AffAsm.parent_from_siblings = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Cover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/MetricSeparated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9e10fe2792/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/affapprox-decomp/challenges/Challenge_separated_net.lean`
- `/tmp/affapprox-decomp/challenges/Challenge_tangent_dimension.lean`
- `/tmp/affapprox-decomp/challenges/Challenge_low_height_point.lean`
- `/tmp/affapprox-decomp/challenges/Challenge_height_bounds.lean`
- `/tmp/affapprox-decomp/challenges/Challenge_PARENT.lean`
- `/tmp/affapprox-decomp/work/Assembly.lean`
- `/tmp/affapprox-decomp/work/AllChecks.lean`
- `/tmp/affapprox-decomp/work/AllChecks.log`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace GMT/Ch07/Submission.lean, which is the compiler context of the children.

Nothing reusable exists:
- No DAG node, decomposition file or accepted math-wiki page proves an a.e. dimension statement for approxTangentPlane, a packing/net lemma, or a Chebyshev selection lemma.
- No dorag_aa_* name occurs anywhere: the 8 DAGs, any node JSON, or the Lean files of all 487 refs.

The pinned Mathlib and SimonGMT supply every tool the child proofs cite:
- measure_biUnion_finset (Measure/Basic.lean:150)
- ENNReal.exists_nat_mul_gt (Basic/ENNReal/Inv.lean:658)
- Nat.findGreatest
- withDensity_absolutelyContinuous (WithDensity.lean:146)
- Measure.measure_compl_support (Support.lean:202)
- lintegral_finsetSum', lintegral_const_mul' (Lebesgue/Add.lean)
- lintegral_mono_set, setLIntegral_const (Lebesgue/Basic.lean:98, 121)
- Submodule.starProjection_orthogonal_val and norm_starProjection_apply_le (Projection/Basic.lean:203, 411)
- ContinuousLinearMap.aestronglyMeasurable_comp₂ (StronglyMeasurable/Lemmas.lean:79); there is no AEStronglyMeasurable.clm_apply
- SimonGMT HasApproximateTangentSpaceAt (Rectifiable.lean:102), whose first conjunct is finrank = n (finrank_eq)
Metric.IsSeparated, IsCover.of_maximal_isSeparated and maximalSeparatedSet also exist, in Cover.lean and CoveringNumbers.lean.

Lean checks:
- All four child types and the parent type elaborate in the exact comparator scope.
- The assembly proves the exact parent type from the three resolved sibling types plus the four child types, using only propext, Classical.choice and Quot.sound.
- Each child also has a sorry-free Lean proof with the same axioms.
