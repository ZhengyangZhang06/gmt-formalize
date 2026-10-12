# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1`
- Child DAG node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1.tangent_le_range-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part B of the parent-supplied proof of simon_submanifold_tangentSpace_eq_range, namely steps 5–7 and the conclusion of step 11. The parent obtains continuity of ψ⁻¹ = invFunOn ψ V on W ∩ M from its sibling theorem chart_inverse_continuous; here it is a hypothesis. The analytic core (parent steps 8–11) is the sibling theorem lift_velocity (Submission.simon_lift_velocity_mem_range_fderiv).

Setting and notation. Fix x₀ ∈ V. Put y₀ := ψ(x₀), A := Dψ(x₀) = fderiv ℝ ψ x₀, and T := range A, a linear subspace of ℝᴺ. Let G be the set of generators of tangentSpace M y₀: v ∈ G iff some γ : ℝ → ℝᴺ is C¹ on (−1,1), maps (−1,1) into M, has γ(0) = y₀ and has derivative v at 0. Thus tangentSpace M y₀ = span G. Note that y₀ ∈ ψ(V) = W ∩ M.

Proof.
1. Differentiability and injectivity at x₀. Since 1 ≤ r and ψ is C^r on V, ψ is C¹ on V; this needs the cast of (1 : ℕ∞) ≤ r to WithTop ℕ∞. V is open and x₀ ∈ V, so ψ is differentiable at x₀. By the last field of IsSimonLocalRepresentation, A = fderiv ℝ ψ x₀ is injective.
2. Reduction. T is a linear subspace and tangentSpace M y₀ = span G, so it suffices to show G ⊆ T. Let v ∈ G, witnessed by γ: γ is C¹ on (−1,1), γ((−1,1)) ⊆ M, γ(0) = y₀, and γ has derivative v at 0.
3. γ stays in W ∩ M near 0 (parent step 6). γ is differentiable, hence continuous, at 0. Since γ(0) = y₀ ∈ W and W is open, γ(t) ∈ W for all t in some neighbourhood of 0. Also (−1,1) is a neighbourhood of 0, and γ(t) ∈ M for t ∈ (−1,1). Hence γ(t) ∈ W ∩ M for all t in some neighbourhood of 0.
4. The lift (parent step 7). Let g := Function.invFunOn ψ V and c(t) := g(γ(t)). Take t in the neighbourhood of step 3. Then γ(t) ∈ W ∩ M = ψ(V), so some point of V is mapped to γ(t), and the defining property of invFunOn gives ψ(c(t)) = γ(t). Thus γ(t) = ψ(c(t)) for all t in a neighbourhood of 0.
5. Continuity of the lift at 0 (parent step 7). Since ψ is injective on V and x₀ ∈ V, g(ψ(x₀)) = x₀, i.e. g(y₀) = x₀. By hypothesis, g is continuous on W ∩ M, in particular continuous within W ∩ M at y₀ ∈ W ∩ M: g(y) → g(y₀) = x₀ as y → y₀ with y ∈ W ∩ M. Since γ is continuous at 0 with γ(0) = y₀, and γ(t) ∈ W ∩ M for t near 0 by step 3, γ tends to y₀ within W ∩ M as t → 0. Composing, c(t) = g(γ(t)) → x₀ as t → 0 along the full neighbourhood filter of 0. This is consistent with c(0) = g(y₀) = x₀.
6. Apply the sibling theorem lift_velocity (Submission.simon_lift_velocity_mem_range_fderiv) to ψ, x₀, c, γ, v. Its hypotheses hold: ψ is differentiable at x₀ and A is injective (step 1); c(t) → x₀ as t → 0 (step 5); γ(t) = ψ(c(t)) for t in a neighbourhood of 0 (step 4); γ has derivative v at 0 (step 2). It yields v ∈ range A = T.
7. Conclusion. Hence G ⊆ T, so tangentSpace M y₀ = span G ⊆ T, i.e. tangentSpace M (ψ x₀) ≤ LinearMap.range (fderiv ℝ ψ x₀).toLinearMap. Since x₀ ∈ V was arbitrary, the theorem follows.

Formal references (Mathlib, pinned snapshot), by step:
- Fields used: Chapter02.IsSimonLocalRepresentation (Poincare/SimonGMT/Chapter02/Submanifold.lean:37) unfolds to IsOpen V ∧ IsOpen W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧ IsProperOnInto ψ V W ∧ ∀ x ∈ V, Injective (fderiv ℝ ψ x). Destructure it with obtain.
- Step 1: ContDiffOn.of_le (Analysis/Calculus/ContDiff/Defs.lean:486) with (by exact_mod_cast hr), ContDiffOn.differentiableOn_one (:582), DifferentiableWithinAt.differentiableAt, IsOpen.mem_nhds.
- Step 2: unfold tangentSpace, then Submodule.span_le (LinearAlgebra/Span/Defs.lean:80).
- Step 3: HasDerivAt.continuousAt, ContinuousAt.preimage_mem_nhds, Ioo_mem_nhds, filter_upwards.
- Step 4: Function.invFunOn_eq (Data/Set/Function.lean:966).
- Step 5: Set.InjOn.leftInvOn_invFunOn (Data/Set/Function.lean:987); ContinuousOn at the point y₀, then ContinuousWithinAt.tendsto; tendsto_nhdsWithin_iff; Filter.Tendsto.comp.

## Key steps

1. 1 ≤ r and V open give differentiability of ψ at x₀, and A = Dψ(x₀) is injective.
2. By span_le it suffices to show that each generator v, the velocity at 0 of a C¹ curve γ in M with γ(0) = ψ(x₀), lies in range A.
3. γ is continuous at 0 and W is open, so γ(t) ∈ W ∩ M for t near 0.
4. c(t) := invFunOn ψ V (γ(t)) satisfies ψ(c(t)) = γ(t) near 0, and c(t) → x₀ by the continuity hypothesis and injectivity on V.
5. The sibling lift_velocity gives v ∈ range A; hence tangentSpace M (ψ x₀) ≤ range A.

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
