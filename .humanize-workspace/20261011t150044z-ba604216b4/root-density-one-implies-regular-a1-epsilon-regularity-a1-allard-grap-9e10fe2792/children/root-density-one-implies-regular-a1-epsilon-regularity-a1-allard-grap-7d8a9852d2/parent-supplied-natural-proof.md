# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1.low_height_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3–5 and the first inequality of Step 6 of the parent proof, i.e. Simon Ch. 5, proof of Lemma 2.5 (book chapter-05.txt lines 309–358): the estimate (1) on B_2(y), the summation over j, Chebyshev's inequality (4) and the choice (5) of x₀. Here it is stated for an arbitrary measure μ and subspace field T, with the a.e. property Q, the integral bounds (ii) and the mass condition (iii) as hypotheses.
Notation:
- For a subspace S and v ∈ ℝ^P, q_S(v) := v − p_S(v); q_S is linear because p_S is.
- For y ∈ F and x ∈ ℝ^P, f_y(x) := ofReal(|q_{T(x)}(x − y)|²) ∈ [0, ∞), and Ψ(x) := Σ_{y∈F} f_y(x).
- For a set E, ∫_E g dμ is the lower Lebesgue integral of g against μ⌞E.
- Closed balls are Borel sets, so μ⌞B̄_t(y)-a.e. point lies in B̄_t(y) (ae_restrict_mem).

1. Measurability. Fix y ∈ F; the map x ↦ x − y is continuous. Apply the continuous bilinear evaluation map (L, v) ↦ L v to the μ-a.e. strongly measurable x ↦ p_{T(x)} and the continuous x ↦ x − y. This shows x ↦ p_{T(x)}(x − y) is μ-a.e. strongly measurable (Mathlib ContinuousLinearMap.aestronglyMeasurable_comp₂, applied to the identity map of the space of continuous linear endomorphisms). Hence x ↦ q_{T(x)}(x − y), its norm and the square of its norm are μ-a.e. strongly measurable. So f_y is μ-a.e. measurable (AEMeasurable.ennreal_ofReal), also for every restriction of μ to a set.

2. Pointwise comparison (Simon (1)). Let y ∈ F and x ∈ B̄_{2r}(y), so |x − y| ≤ 2r. Put A := |q_{T(x)}(x − y)|² ≥ 0.
- If x = y, then x − y = 0 and q_{T(x)}(0) = 0, so A = 0 and A ≤ (2r)^m·(A/|x − y|^m) holds as 0 ≤ 0.
- If x ≠ y, then |x − y|^m > 0 and |x − y|^m ≤ (2r)^m (powers are monotone on [0, ∞)). Since A/|x − y|^m ≥ 0, A = |x − y|^m·(A/|x − y|^m) ≤ (2r)^m·(A/|x − y|^m).
Since (2r)^m ≥ 0, ofReal((2r)^m·b) = ofReal((2r)^m)·ofReal(b) for every real b (ENNReal.ofReal_mul). Hence f_y(x) ≤ ofReal((2r)^m)·ofReal(A/|x − y|^m) for every x ∈ B̄_{2r}(y).

3. The integral of each f_y. Let y ∈ F. For x ∈ B̄_r(ξ), dist(x, y) ≤ dist(x, ξ) + dist(ξ, y) ≤ r + r = 2r by (i), so B̄_r(ξ) ⊆ B̄_{2r}(y). Combine four facts:
- monotonicity of the integral in the domain (lintegral_mono_set);
- Step 2 for μ⌞B̄_{2r}(y)-a.e. x (lintegral_mono_ae);
- a finite constant comes out of a lower integral (lintegral_const_mul', since ofReal((2r)^m) ≠ ∞);
- hypothesis (ii).
They give ∫_{B̄_r(ξ)} f_y dμ ≤ ∫_{B̄_{2r}(y)} f_y dμ ≤ ofReal((2r)^m)·∫_{B̄_{2r}(y)} ofReal(|q_{T(x)}(x − y)|²/|x − y|^m) dμ(x) ≤ ofReal((2r)^m)·ofReal(c) = ofReal((2r)^m·c).

4. Summation. By Step 1 each f_y is a.e. measurable for μ⌞B̄_r(ξ), so the integral of the finite sum is the sum of the integrals (lintegral_finsetSum'). By Step 3, ∫_{B̄_r(ξ)} Ψ dμ = Σ_{y∈F} ∫_{B̄_r(ξ)} f_y dμ ≤ Σ_{y∈F} ofReal((2r)^m·c) = (#F)·ofReal((2r)^m·c).

5. Choice of x₀ (Simon (4)–(5)), by contradiction. Suppose that for every x ∈ B̄_s(ξ) with Q(x) there is y ∈ F with |q_{T(x)}(y − x)|² > λ.
(a) Lower bound at such x. By linearity q_{T(x)}(x − y) = −q_{T(x)}(y − x), so |q_{T(x)}(x − y)| = |q_{T(x)}(y − x)|. Hence f_y(x) = ofReal(|q_{T(x)}(y − x)|²) ≥ ofReal(λ) (ofReal is monotone), and Ψ(x) ≥ f_y(x) ≥ ofReal(λ) because every summand of Ψ is ≥ 0 (Finset.single_le_sum).
(b) This holds μ⌞B̄_s(ξ)-a.e. Q holds μ-a.e., hence μ⌞B̄_s(ξ)-a.e. (ae_restrict_of_ae), and μ⌞B̄_s(ξ)-a.e. point lies in B̄_s(ξ). So Ψ ≥ ofReal(λ) holds μ⌞B̄_s(ξ)-a.e.
(c) Contradiction. Since s ≤ r, B̄_s(ξ) ⊆ B̄_r(ξ). By the integral of a constant over a set (setLIntegral_const), lintegral_mono_ae, lintegral_mono_set and Step 4,
ofReal(λ)·μ(B̄_s(ξ)) = ∫_{B̄_s(ξ)} ofReal(λ) dμ ≤ ∫_{B̄_s(ξ)} Ψ dμ ≤ ∫_{B̄_r(ξ)} Ψ dμ ≤ (#F)·ofReal((2r)^m·c).
This contradicts (iii).

6. Conclusion. The supposition of Step 5 fails. Hence there is x₀ ∈ B̄_s(ξ) with Q(x₀) and |q_{T(x₀)}(y − x₀)|² ≤ λ, i.e. |(y − x₀) − p_{T(x₀)}(y − x₀)|² ≤ λ, for every y ∈ F. ∎

## Key steps

1. x ↦ |(x − y) − p_{T(x)}(x − y)|² is μ-a.e. measurable because x ↦ p_{T(x)} is a.e. strongly measurable (aestronglyMeasurable_comp₂).
2. On B̄_{2r}(y), |q|² ≤ (2r)^m·|q|²/|x − y|^m; with B̄_r(ξ) ⊆ B̄_{2r}(y) and (ii) this gives ∫_{B̄_r(ξ)} |q_{T(x)}(x − y)|² dμ ≤ (2r)^m c.
3. Summing over y ∈ F gives ∫_{B̄_r(ξ)} Ψ dμ ≤ #F·(2r)^m c, where Ψ(x) = Σ_y |q_{T(x)}(x − y)|².
4. If every Q-point x of B̄_s(ξ) had some |q_{T(x)}(y − x)|² > λ, then Ψ ≥ λ a.e. on B̄_s(ξ), so λ·μ(B̄_s(ξ)) ≤ #F·(2r)^m c, contradicting (iii).

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
