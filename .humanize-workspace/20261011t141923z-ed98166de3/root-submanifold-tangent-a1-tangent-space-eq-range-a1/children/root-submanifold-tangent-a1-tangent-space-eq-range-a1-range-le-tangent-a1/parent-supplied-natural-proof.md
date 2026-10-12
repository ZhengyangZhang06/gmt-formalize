# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1`
- Child DAG node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1.range_le_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part A (steps 1–4) of the parent-supplied proof of simon_submanifold_tangentSpace_eq_range. This is Simon, Introduction to GMT, Ch. 2, 4.3, p. 55; the printed text only says 'one readily checks'. That argument uses only that V is open, ψ is C¹ on V and ψ maps V into M, so this child is stated under exactly these hypotheses. The parent obtains them from IsSimonLocalRepresentation r M V W ψ and 1 ≤ r.

Setting and notation. |·| denotes the Euclidean norms. Fix x₀ ∈ V. Put y₀ := ψ(x₀) and A := Dψ(x₀) = fderiv ℝ ψ x₀. Let G be the set of generators of tangentSpace M y₀: v ∈ G iff there is γ : ℝ → ℝᴺ that is C¹ on (−1,1), maps (−1,1) into M, has γ(0) = y₀ and has derivative v at 0. Thus tangentSpace M y₀ = span G is a linear subspace of ℝᴺ containing G. The claim LinearMap.range A ≤ tangentSpace M y₀ means: A w ∈ tangentSpace M y₀ for every w ∈ ℝⁿ.

Proof.
1. Differentiability. V is open and x₀ ∈ V, so V is a neighbourhood of x₀. ψ is C¹ on V, hence differentiable within V at x₀. Since V is a neighbourhood of x₀, ψ is differentiable at x₀, with Fréchet derivative A = fderiv ℝ ψ x₀ at x₀.
2. Let w ∈ ℝⁿ. If w = 0, then A w = 0 ∈ tangentSpace M y₀, because a linear subspace contains 0. Now let w ≠ 0, so |w| > 0. Since V is open, choose ρ > 0 with B(x₀, ρ) ⊆ V, where B is the open ball. Put κ := ρ/(2|w|) > 0, ℓ(t) := x₀ + (κ t) w and γ(t) := ψ(ℓ(t)) for t ∈ ℝ.
3. Let t ∈ (−1,1). Then |ℓ(t) − x₀| = κ|t||w| = (ρ/2)|t| < ρ, so ℓ(t) ∈ B(x₀, ρ) ⊆ V. Hence γ(t) = ψ(ℓ(t)) ∈ M, because ψ maps V into M. Thus ℓ maps (−1,1) into V and γ maps (−1,1) into M. The map ℓ is affine, hence C^∞ and in particular C¹ on ℝ. ψ is C¹ on V and ℓ maps (−1,1) into V, so by the composition rule for C¹ maps on sets, γ = ψ ∘ ℓ is C¹ on (−1,1). Also ℓ(0) = x₀, so γ(0) = ψ(x₀) = y₀.
4. The map t ↦ x₀ + (κ t) w has derivative κ w at 0. By step 1, ψ has Fréchet derivative A at ℓ(0) = x₀. The chain rule shows that γ = ψ ∘ ℓ has derivative A(κ w) = κ·A w at 0, using linearity of A. Together with step 3, γ witnesses κ·A w ∈ G ⊆ tangentSpace M y₀. Since tangentSpace M y₀ is a linear subspace and κ ≠ 0, A w = κ⁻¹·(κ·A w) ∈ tangentSpace M y₀.
5. Conclusion. Steps 2–4 give A w ∈ tangentSpace M y₀ for every w ∈ ℝⁿ, i.e. LinearMap.range (fderiv ℝ ψ x₀).toLinearMap ≤ tangentSpace M (ψ x₀). Since x₀ ∈ V was arbitrary, the theorem follows.

Formal references (Mathlib, pinned snapshot), by step:
- Step 1: ContDiffOn.differentiableOn_one (Analysis/Calculus/ContDiff/Defs.lean:582), DifferentiableWithinAt.differentiableAt with IsOpen.mem_nhds, DifferentiableAt.hasFDerivAt.
- Step 2: Metric.isOpen_iff, norm_pos_iff.
- Step 3: ContDiffOn.comp (Analysis/Calculus/ContDiff/Comp.lean:125) with ContDiff.contDiffOn, where contDiff_const.add ((contDiff_const.mul contDiff_id).smul contDiff_const) gives ContDiff ℝ 1 ℓ; MapsTo.comp.
- Step 4: HasDerivAt.const_mul, HasDerivAt.smul_const and HasDerivAt.const_add for ℓ; HasFDerivAt.comp_hasDerivAt (Analysis/Calculus/Deriv/Comp.lean:374); unfold tangentSpace, then Submodule.subset_span (LinearAlgebra/Span/Defs.lean:75); map_smul, Submodule.smul_mem, smul_smul, inv_mul_cancel₀.

## Key steps

1. ψ is C¹ on the open set V, so it is differentiable at x₀ with derivative A = fderiv ℝ ψ x₀.
2. For w = 0, Aw = 0 lies in the subspace. For w ≠ 0, choose B(x₀, ρ) ⊆ V and κ = ρ/(2|w|).
3. The curve γ(t) = ψ(x₀ + κ t w) is C¹ on (−1,1), maps (−1,1) into ψ(V) ⊆ M, and has γ(0) = ψ(x₀).
4. Chain rule: γ′(0) = κ·Aw, so κ·Aw is a generator. Dividing by κ gives Aw ∈ tangentSpace M (ψ x₀); hence range A ≤ tangentSpace M (ψ x₀).

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
