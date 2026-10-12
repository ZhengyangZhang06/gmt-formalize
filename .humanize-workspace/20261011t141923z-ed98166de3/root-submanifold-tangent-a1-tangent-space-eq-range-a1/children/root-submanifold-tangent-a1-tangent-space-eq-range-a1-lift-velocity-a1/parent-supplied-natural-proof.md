# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1`
- Child DAG node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1.lift_velocity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 8–11 of the parent-supplied proof of simon_submanifold_tangentSpace_eq_range, i.e. the analytic core of Part B. There, steps 6–7 produce the lift c(t) and the factorisation γ(t) = ψ(c(t)); here they are hypotheses (iii) and (iv). Differentiability of c is neither assumed nor used.

Setting and notation. A := fderiv ℝ ψ x₀ and |·| denotes the Euclidean norms. By hypothesis (iv), fix τ > 0 with γ(t) = ψ(c(t)) for all |t| < τ.

Proof.
0. Base point.
(i) c(0) = x₀. Let U be any neighbourhood of x₀. By hypothesis (iii), c⁻¹(U) is a neighbourhood of 0, so it contains 0 and c(0) ∈ U. Since ℝⁿ is Hausdorff, c(0) = x₀.
(ii) Taking t = 0 in the factorisation gives γ(0) = ψ(c(0)) = ψ(x₀).
1. Differentiability. ψ is differentiable at x₀ with derivative A. Write e(x) := ψ(x) − ψ(x₀) − A(x − x₀). Then for every ε > 0 there is δ_ε > 0 with |e(x)| ≤ ε|x − x₀| whenever |x − x₀| < δ_ε.
2. Lower bound (parent step 8). A is injective and ℝⁿ is finite-dimensional, so there is λ > 0 with |Aζ| ≥ λ|ζ| for all ζ ∈ ℝⁿ. If n = 0, take λ = 1; then ζ = 0 always. Otherwise ζ ↦ |Aζ| is continuous and, by injectivity, positive on the compact nonempty unit sphere, so it has a positive minimum λ there. For ζ ≠ 0, apply this to ζ/|ζ|.
3. Bounded difference quotients (parent step 9). Since c(t) → x₀ as t → 0, there is τ₁ ∈ (0, τ] with |c(t) − x₀| < δ_{λ/2} for |t| < τ₁. For such t, use γ(t) = ψ(c(t)) and γ(0) = ψ(x₀), step 1 with ε = λ/2, and step 2:
|γ(t) − γ(0)| = |A(c(t) − x₀) + e(c(t))| ≥ λ|c(t) − x₀| − (λ/2)|c(t) − x₀| = (λ/2)|c(t) − x₀|.
Since γ has derivative v at 0, there is τ₂ ∈ (0, τ₁] with |γ(t) − γ(0) − t v| ≤ |t| for |t| < τ₂. Then |γ(t) − γ(0)| ≤ (|v| + 1)|t|, so (λ/2)|c(t) − x₀| ≤ (|v| + 1)|t| for |t| < τ₂. Hence ζ(t) := t⁻¹(c(t) − x₀) satisfies |ζ(t)| ≤ C := 2(|v| + 1)/λ for 0 < |t| < τ₂.
4. Compactness (parent step 10). Let t_j := τ₂/(j + 2) for j ∈ ℕ. Then 0 < t_j < τ₂, t_j → 0 and |ζ(t_j)| ≤ C. By Bolzano–Weierstrass in ℝⁿ, there is a strictly increasing sequence j_k such that s_k := t_{j_k} gives ζ(s_k) → ζ for some point ζ ∈ ℝⁿ. Still s_k ≠ 0 and s_k → 0.
5. Identification of the limit (parent step 11). For every k, 0 < s_k < τ, so γ(s_k) = ψ(c(s_k)) and
(γ(s_k) − γ(0))/s_k = (A(c(s_k) − x₀) + e(c(s_k)))/s_k = Aζ(s_k) + e(c(s_k))/s_k.
(a) The left side tends to v, because γ has derivative v at 0, s_k → 0 and s_k ≠ 0.
(b) Aζ(s_k) → Aζ, because A is linear on the finite-dimensional ℝⁿ, hence continuous.
(c) e(c(s_k))/s_k → 0. Let ε > 0. Since s_k → 0 and c(t) → x₀, we have c(s_k) → x₀, so |c(s_k) − x₀| < δ_ε for all large k. Then |e(c(s_k))/s_k| ≤ ε|c(s_k) − x₀|/|s_k| = ε|ζ(s_k)| ≤ εC.
By (a)–(c) and uniqueness of limits in ℝᴺ, v = Aζ. Hence v ∈ range A = LinearMap.range (fderiv ℝ ψ x₀).toLinearMap. This proves the theorem.

Remark: an alternative ending. Steps 0–5 already prove the theorem. A formalizer may replace steps 4–5 by the following equally complete argument.
(i) By step 1 composed with c(t) → x₀, e(c(t)) = o(|c(t) − x₀|) as t → 0.
(ii) Step 3 gives |c(t) − x₀| ≤ C|t| for |t| < τ₂ (trivially at t = 0), so c(t) − x₀ = O(t). Hence e(c(t)) = o(t), and t⁻¹e(c(t)) → 0 as t → 0.
(iii) For 0 < |t| < τ, A(t⁻¹(c(t) − x₀)) = t⁻¹(γ(t) − γ(0)) − t⁻¹e(c(t)). The first term tends to v along t → 0, t ≠ 0, because γ has derivative v at 0. So A(t⁻¹(c(t) − x₀)) → v along t → 0, t ≠ 0, a nontrivial filter on ℝ.
(iv) Every A(t⁻¹(c(t) − x₀)) lies in range A, a finite-dimensional and hence closed subspace of ℝᴺ. Therefore v lies in the closure of range A, which is range A itself.
This is the route used for the scratch Lean check.

Formal references (Mathlib, pinned snapshot), by step:
- Step 0: tendsto_nhds_unique with tendsto_pure_nhds and pure_le_nhds; Filter.Eventually.self_of_nhds.
- Step 1: DifferentiableAt.hasFDerivAt and HasFDerivAt.isLittleO (hasFDerivAt_iff_isLittleO, Analysis/Calculus/FDeriv/Defs.lean:225).
- Step 2: LinearMap.exists_antilipschitzWith (Analysis/Normed/Module/FiniteDimension.lean:231) applied to A.toLinearMap with LinearMap.ker_eq_bot, then ContinuousLinearMap.bound_of_antilipschitz (Analysis/Normed/Operator/ContinuousLinearMap.lean:106). This gives |ζ| ≤ K|Aζ| with K > 0, i.e. λ = 1/K.
- Step 3: HasDerivAt.isLittleO (hasDerivAt_iff_isLittleO, Analysis/Calculus/Deriv/Basic.lean:286) and Asymptotics.isLittleO_iff.
- Step 4: tendsto_subseq_of_bounded (Topology/MetricSpace/Sequences.lean:38).
- Step 5: hasDerivAt_iff_tendsto_slope (Analysis/Calculus/Deriv/Slope.lean:73).
- Alternative ending: Asymptotics.IsLittleO.comp_tendsto and IsLittleO.trans_isBigO (Analysis/Asymptotics/Basic.lean:247, 306), IsLittleO.tendsto_inv_smul_nhds_zero (Analysis/Asymptotics/Lemmas.lean:391), HasDerivAt.tendsto_slope, slope_def_module, Submodule.closed_of_finiteDimensional (Topology/Algebra/Module/FiniteDimension.lean:531), mem_closure_of_tendsto (Topology/Neighborhoods.lean:364), IsClosed.closure_eq.

## Key steps

1. c(0) = x₀ (unpunctured limit in a Hausdorff space) and γ(0) = ψ(x₀); the remainder e(x) = ψ(x) − ψ(x₀) − A(x − x₀) is o(|x − x₀|).
2. Injectivity of A on the finite-dimensional ℝⁿ gives λ > 0 with |Aζ| ≥ λ|ζ|.
3. Near 0, (λ/2)|c(t) − x₀| ≤ |γ(t) − γ(0)| ≤ (|v| + 1)|t|, so ζ(t) = (c(t) − x₀)/t is bounded by C = 2(|v| + 1)/λ.
4. Bolzano–Weierstrass along t_j = τ₂/(j + 2) gives s_k → 0, s_k ≠ 0, ζ(s_k) → ζ.
5. (γ(s_k) − γ(0))/s_k = Aζ(s_k) + e(c(s_k))/s_k tends both to v and to Aζ, so v = Aζ ∈ range A.

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch02/Contract.lean <snapshot>/project/GMT/Ch02/{Contract,Submission}.lean; rg -n '^def tangentSpace|^abbrev Rn' <snapshot>/project/GMT/Ch02/Contract.lean; rg -n 'Submission\.' <snapshot>/project`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `rg -n 'theorem ContDiffOn.differentiableOn|theorem ContDiffOn.of_le|theorem ContDiffOn.comp |theorem HasFDerivAt.comp_hasDerivAt |theorem tendsto_subseq_of_bounded|exists_antilipschitzWith|theorem InjOn.leftInvOn_invFunOn|theorem invFunOn_mem|theorem invFunOn_eq|theorem span_le |theorem subset_span |hasDerivAt_iff_isLittleO|theorem hasDerivAt_iff_tendsto_slope' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem HasFDerivAt.isLittleO|alias.*HasFDerivAt.isLittleO|bound_of_antilipschitz|theorem Submodule.closed_of_finiteDimensional|theorem mem_closure_of_tendsto|theorem IsLittleO.comp_tendsto|theorem IsLittleO.trans_isBigO|tendsto_inv_smul_nhds_zero' <snapshot>/mathlib/Mathlib`
- `sed -n 845,875p book/chapter-02.txt (printed Simon 4.1-4.3)`
- `python3 -I scope.py / gen.py (verifier/gmt-compare.py contract_scope + child_modules, verifier/lean_contract.py validate_lean_statement) on the three lean_statements; lake env lean test/Challenge_{range_le_tangent,lift_velocity,tangent_le_range}.lean against a scratch build of GMT.Ch02.Submission`
- `lake env lean test/EndToEnd.lean (full proofs of the three children, stubbed simon_submanifold_chart_inverse_continuousOn with its dag.json type, selected frozen type assembled by le_antisymm, #print axioms, #check with pp.numericTypes)`
- `python3 -I lean_name/lean_statement scan of dag.json and nodes/*/decomposition-v*.json; rg -l <three names> lake-packages-25730c7c/simongmt lake-packages-25730c7c/mathlib/Mathlib .humanize; git grep -l <three names> over all 174 refs`
- `git show <accepted c1_sard/lipschitz commits>:GMT/Ch02/Submission.lean | grep '^theorem' (Submission.X layout; no existing tangentSpace inclusion lemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Asymptotics/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-submanifold-tangent-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-submanifold-tangent-a1-tangent-space-eq-range-a1/parent-child-handoff.json`
- `/tmp/gmt-ch02-tser-1rtKRC/test/EndToEnd.lean`

Contract.lean defines Rn (line 48, EuclideanSpace ℝ (Fin n)) and tangentSpace (line 86, the span of velocities at 0 of C¹ curves (−1,1) → M through y). It is byte-identical in the workspace, in the snapshot's project/ (Contract and Submission), and in the scratch build. The snapshot has no Submission.X declarations. SimonGMT Submanifold.lean:37 fixes IsSimonLocalRepresentation as IsOpen V ∧ IsOpen W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧ IsProperOnInto ψ V W ∧ ∀ x ∈ V, Injective (fderiv ℝ ψ x); every child uses exactly these fields. Neither SimonGMT, Mathlib nor any accepted Submission commit has a lemma relating tangentSpace to range Dψ.

Mathlib supplies everything the children need: ContDiffOn.of_le (ContDiff/Defs.lean:486), ContDiffOn.differentiableOn_one (:582), ContDiffOn.comp (ContDiff/Comp.lean:125), HasFDerivAt.comp_hasDerivAt (Deriv/Comp.lean:374), hasFDerivAt_iff_isLittleO (FDeriv/Defs.lean:225), hasDerivAt_iff_isLittleO (Deriv/Basic.lean:286), hasDerivAt_iff_tendsto_slope (Deriv/Slope.lean:73), LinearMap.exists_antilipschitzWith (Normed/Module/FiniteDimension.lean:231), ContinuousLinearMap.bound_of_antilipschitz (Normed/Operator/ContinuousLinearMap.lean:106), IsLittleO.comp_tendsto and IsLittleO.trans_isBigO (Asymptotics/Basic.lean:247, 306), IsLittleO.tendsto_inv_smul_nhds_zero (Asymptotics/Lemmas.lean:391), Submodule.closed_of_finiteDimensional (Topology/Algebra/Module/FiniteDimension.lean:531), mem_closure_of_tendsto (Topology/Neighborhoods.lean:364), tendsto_subseq_of_bounded (MetricSpace/Sequences.lean:38), Function.invFunOn_eq and Set.InjOn.leftInvOn_invFunOn (Data/Set/Function.lean:966, 987), and Submodule.subset_span and span_le (LinearAlgebra/Span/Defs.lean:75, 80).

All three child statements elaborate in the comparator's replayed Contract scope. Each was fully proved in scratch Lean using only propext, Classical.choice and Quot.sound. The selected frozen type follows from them plus the sibling chart_inverse_continuous by le_antisymm. No proposed name collides with dag.json, pending decompositions, git refs, SimonGMT or Mathlib.
