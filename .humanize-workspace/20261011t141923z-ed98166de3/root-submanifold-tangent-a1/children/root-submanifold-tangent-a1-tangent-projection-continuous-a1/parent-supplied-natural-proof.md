# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_tangent-a1`
- Child DAG node: `root.submanifold_tangent-a1.tangent_projection_continuous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent-supplied proof of simon_submanifold_tangent_basics. It uses three sibling theorems: chart_inverse_continuous (parent step 1), tangent_space_eq_range (parent steps 2–4) and range_projection_continuous (parent step 7).

Proof.
1. Fix y₀ ∈ M. By IsSimonSubmanifold, 1 ≤ r, and there are V, W, ψ with y₀ ∈ W and IsSimonLocalRepresentation r M V W ψ. Put g := Function.invFunOn ψ V and P := tangentProjection M.
2. For y ∈ W ∩ M = ψ(V), some a ∈ V has ψ(a) = y, so by the definition of invFunOn, g(y) ∈ V and ψ(g(y)) = y.
3. Formula for P on W ∩ M. Let y ∈ W ∩ M and x := g(y) ∈ V. By tangent_space_eq_range, which applies since 1 ≤ r, tangentSpace M (ψ x) = range Dψ(x) with Dψ(x) = fderiv ℝ ψ x. Since ψ(x) = y, tangentSpace M y = range Dψ(g(y)). P(y) is the orthogonal projection onto tangentSpace M y, so P(y) = P_{range Dψ(g(y))} for every y ∈ W ∩ M.
4. The right side is continuous on W ∩ M.
(a) By chart_inverse_continuous, g is continuous on W ∩ M, and by step 2 it maps W ∩ M into V.
(b) ψ is C^r with r ≥ 1 on the open set V, so x ↦ Dψ(x) is continuous on V. Also Dψ(x) is injective for every x ∈ V (IsSimonLocalRepresentation), so x ↦ Dψ(x) maps V into the set S of injective linear maps.
(c) By range_projection_continuous, A ↦ P_{range A} is continuous on S.
Each map sends its domain into the set on which the next map is continuous. By the composition rule for maps continuous on sets, y ↦ P_{range Dψ(g(y))} is continuous on W ∩ M.
5. By steps 3 and 4, P coincides on W ∩ M with a function that is continuous on W ∩ M, so P is continuous on W ∩ M. In particular, since y₀ ∈ W ∩ M, P is continuous within W ∩ M at y₀.
6. W is open and contains y₀, so W is a neighbourhood of y₀. Therefore the filters of neighbourhoods of y₀ within W ∩ M and within M coincide, and P is continuous within M at y₀.
7. Since y₀ ∈ M was arbitrary, ContinuousOn (tangentProjection M) M.

Formal references (Mathlib): Function.invFunOn_mem, Function.invFunOn_eq, ContDiffOn.continuousOn_fderiv_of_isOpen (Analysis/Calculus/ContDiff/Defs.lean:916), ContinuousOn.comp, ContinuousOn.congr, continuousWithinAt_inter (Topology/ContinuousOn.lean:259).

## Key steps

1. Fix y₀ ∈ M and a local representation (V, W, ψ) with y₀ ∈ W. Then g = invFunOn ψ V maps W ∩ M into V, and ψ ∘ g = id there.
2. By tangent_space_eq_range, tangentProjection M y = P_{range Dψ(g(y))} for y ∈ W ∩ M.
3. Three maps compose to a function continuous on W ∩ M: g (chart_inverse_continuous), x ↦ Dψ(x) (C¹ on open V, with injective values), and A ↦ P_{range A} (range_projection_continuous).
4. W is a neighbourhood of y₀, so continuity within W ∩ M at y₀ is the same as continuity within M at y₀.

## Reference use

### local-project

Queries:
- `rg -n '^def tangentSpace|^def tangentProjection|^abbrev Rn' project/GMT/Ch02/Contract.lean`
- `rg -n 'Submission\.' project`
- `rg -n 'isEmbedding_chartMap|exists_open_image_eq_inter|IsSimonLocalRepresentation\.|IsSimonSubmanifold\.' lake-packages-25730c7c/simongmt (then full reads of Chapter02/Submanifold.lean and Chapter02/SubmanifoldTopology.lean)`
- `rg -n 'starProjection|orthogonalProjection' -l lake-packages-25730c7c/simongmt/Poincare; sed -n 780,900p Chapter08/Varifold.lean`
- `rg -n 'theorem IsLocallyClosed\.(measurableSet|nullMeasurableSet)|IsLocallyClosed.measurableSet' mathlib/Mathlib; rg -n '^theorem|^lemma' mathlib/Mathlib/Topology/LocallyClosed.lean`
- `rg -n 'class HasOrthogonalProjection|def starProjection|theorem eq_starProjection_of_mem_of_inner_eq_zero|isSymmetricProjection_iff_eq_coe_starProjection_range' mathlib/Mathlib/Analysis/InnerProductSpace/`
- `rg -n 'theorem inverse_continuousAt' mathlib/Mathlib/Analysis/Normed/Ring/Units.lean; rg -n '^def adjoint|theorem adjoint_inner_left' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem ContDiffOn.differentiableOn' mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `rg -n '^noncomputable def invFunOn|^theorem invFunOn_mem|^theorem invFunOn_eq|^theorem InjOn.leftInvOn_invFunOn' mathlib/Mathlib/Data/Set/Function.lean`
- `rg -n 'theorem tendsto_subseq_of_bounded|theorem IsCompact.tendsto_subseq |theorem mem_closure_iff_seq_limit|theorem isOpen_iUnion_countable|theorem continuousWithinAt_inter |exists_antilipschitzWith|theorem ContinuousLinearMap.isOpen_injective|theorem HasFDerivAt.comp_hasDerivAt ' mathlib/Mathlib`
- `python3 -I gen_checks.py (loads verifier/gmt-compare.py child_modules + contract_scope and verifier/lean_contract.py validate_lean_statement) on the five lean_statements; lake env lean final/NodeChallenge_00..04.lean against a scratch build of GMT.Ch02.Submission`
- `lake env lean final/FinalAssembly.lean (real proofs of chart_inverse_continuous, range_projection_continuous, submanifold_measurable; sorried tangent_space_eq_range; tangent_projection_continuous from siblings; parent frozen type assembled; #print axioms)`
- `python3 -I lean_name scan of dag.json; grep lean_name nodes/*/decomposition-v*.json; rg -l 'simon_submanifold_' lake-packages-25730c7c/simongmt/Poincare; git grep -l 'simon_submanifold_' (snapshot mathlib)`
- `sed -n 845,875p book/chapter-02.txt (printed Simon 4.1-4.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/LocallyClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-submanifold-tangent-a1/parent-child-handoff.json`
- `/tmp/gmt-ch02-subtan-r3I2jM/final/FinalAssembly.lean`

Contract.lean:48/86/91 fixes Rn, tangentSpace (the span of velocities of C¹ curves (−1,1) → M) and tangentProjection (Submodule.starProjection). The project snapshot has no Submission.* declarations. The pinned SimonGMT Submanifold.lean (IsProperOnInto:30, IsSimonLocalRepresentation:37, IsSimonSubmanifold:48) matches the hypotheses used by every child. SubmanifoldTopology.lean proves isProperMap_chartMap:54, isEmbedding_chartMap:90 and exists_open_image_eq_inter:100, which state chart_inverse_continuous in closed-embedding form. That module is not imported by the Contract, but a child file under GMT/Ch02 may import it. SimonGMT has no tangentSpace = range Dψ theorem, no measurability theorem for submanifolds, and no continuity theorem for range projections. Its Chapter08/Varifold.lean projection formula is specific to matrices and its Grassmannian. Mathlib supplies everything the children need: HasOrthogonalProjection (a Prop class, Projection/Basic.lean:48), starProjection:131, eq_starProjection_of_mem_of_inner_eq_zero:180, ContinuousLinearMap.adjoint (Adjoint.lean:112), NormedRing.inverse_continuousAt (Normed/Ring/Units.lean:183), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916), invFunOn and its lemmas (Data/Set/Function.lean:953-987), tendsto_subseq_of_bounded (MetricSpace/Sequences.lean:38), IsCompact.tendsto_subseq (Sequences.lean:298), mem_closure_iff_seq_limit (Sequences.lean:108), isOpen_iUnion_countable (Bases.lean:932), continuousWithinAt_inter (ContinuousOn.lean:259), LinearMap.exists_antilipschitzWith (FiniteDimension.lean:231) and HasFDerivAt.comp_hasDerivAt (Deriv/Comp.lean:374). Mathlib has no IsLocallyClosed.measurableSet. All five child statements elaborate in the comparator's replayed Contract scope, and the frozen parent type follows from them by a one-line term. Scratch Lean proofs of chart_inverse_continuous, range_projection_continuous and submanifold_measurable depend only on propext, Classical.choice and Quot.sound. tangent_projection_continuous compiles from its three sibling statements. No proposed lean_name collides with dag.json (41 nodes), with pending decompositions, or with SimonGMT or Mathlib.
