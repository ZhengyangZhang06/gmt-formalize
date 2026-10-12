# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1.unit_ball_dense_seq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–2 of the parent node's supplied proof of regcomp_covector_field_near_maximizer (finite dimensionality of Λ^n via the injective coefficient map, separability, countable dense subset of the unit ball B, enumeration), specialized to output a sequence.

Notation:
- ℝ^P = Euclid P = EuclideanSpace ℝ (Fin P), with standard orthonormal basis e_i = EuclideanSpace.basisFun (Fin P) ℝ i.
- Λ^n = Covector (Euclid P) n, the continuous alternating n-linear forms on ℝ^P, with Mathlib's normed-space structure and the topology it induces. This is the topology in which `closure` is taken in the statement, and the one for which every element of MultiVector P n = Λ^n →L[ℝ] ℝ is continuous.
- For J : Fin n → Fin P, e∘J := (e_{J(0)}, …, e_{J(n−1)}).
- |α|_E := covectorEuclideanNorm α = √(Σ_{I : Fin n → Fin P, I strictly increasing} α(e∘I)²) (SimonGMT Chapter06/Mass.lean).

Fix P and n.

1. (Λ^n is finite dimensional.) Define ev : Λ^n → ((Fin n → Fin P) → ℝ) by ev(α)(J) := α(e∘J). It is ℝ-linear, since (α + β)(v) = α(v) + β(v) and (c • α)(v) = c · α(v) for every n-tuple v.
   It is injective. Suppose ev α = ev β. Then the underlying multilinear maps α.toMultilinearMap and β.toMultilinearMap take the same value on every tuple (e_{J(0)}, …, e_{J(n−1)}) of basis vectors. A multilinear map is determined by these values: writing each argument as v_i = Σ_k c_{ik} e_k, multilinearity gives α(v) = Σ_{J : Fin n → Fin P} (∏_i c_{i,J(i)}) α(e∘J), and likewise for β. In Mathlib this is Module.Basis.ext_multilinear, applied with the basis (EuclideanSpace.basisFun (Fin P) ℝ).toBasis in every slot. Hence α.toMultilinearMap = β.toMultilinearMap, so α v = β v for every v, and α = β by extensionality.
   The target (Fin n → Fin P) → ℝ is a finite product of copies of ℝ, hence finite dimensional, so FiniteDimensional.of_injective yields FiniteDimensional ℝ Λ^n. Mathlib has no global instance FiniteDimensional ℝ (Covector (Euclid P) n), so establish it as a local `have`; instance search then uses it in step 2.

2. (Separability.) A finite-dimensional real normed space is proper (instance FiniteDimensional.proper_real: closed balls are compact). A proper metric space is second countable (instance secondCountable_of_proper), and a second-countable space is separable. Therefore every subset of Λ^n is separable (TopologicalSpace.IsSeparable.of_separableSpace); in particular so is B := {β ∈ Λ^n : |β|_E ≤ 1}.

3. (Countable dense subset inside B.) Λ^n is a metric space, hence pseudo-metrizable. So the separable set B contains a countable set D ⊆ B with B ⊆ closure D (TopologicalSpace.IsSeparable.exists_countable_dense_subset).

4. (D is nonempty.) |0|_E = 0 ≤ 1 (covectorEuclideanNorm_zero), so 0 ∈ B ⊆ closure D. If D were empty, closure D = closure ∅ = ∅ could not contain 0. Hence D is nonempty.

5. (Enumeration.) A nonempty countable set is the range of a sequence (Set.Countable.exists_eq_range): there is b : ℕ → Λ^n with D = range b.

6. (Conclusion.) For every k, b k ∈ range b = D ⊆ B, i.e. covectorEuclideanNorm (b k) ≤ 1. If β ∈ Λ^n satisfies covectorEuclideanNorm β ≤ 1, then β ∈ B ⊆ closure D = closure (range b). This is the claim. (Neither closedness of B nor continuity of |·|_E is needed.) ∎

## Key steps

1. The coefficient map α ↦ (J ↦ α(e∘J)) into (Fin n → Fin P) → ℝ is linear and injective (Module.Basis.ext_multilinear), so Λ^n is finite dimensional (FiniteDimensional.of_injective, established locally).
2. Finite dimensional ⇒ proper ⇒ second countable ⇒ separable, so B = {β : |β|_E ≤ 1} is separable (IsSeparable.of_separableSpace).
3. IsSeparable.exists_countable_dense_subset gives a countable D ⊆ B with B ⊆ closure D; D ≠ ∅ because 0 ∈ B.
4. Enumerate D = range b (Set.Countable.exists_eq_range); then |b k|_E ≤ 1 for all k and every β with |β|_E ≤ 1 lies in closure (range b).

## Reference use

### local-project

Queries:
- `cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (IDENTICAL)`
- `python3 -I scan of dag.json nodes for lean_name/lean_statement matching finitedimensional|separab|dense|covector|selection|stronglymeasurable|regcomp_ (found imsupp_covector_finiteDimensional, identical FiniteDimensional type, status decomposing; no name collision)`
- `grep -l 'regcomp_covector_unit_ball_dense_seq\|regcomp_covector_first_hit_selection' over 125 .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean, GMT/Ch07/Submission.lean, dag.json (no match)`
- `grep -rn 'FiniteDimensional ℝ (Covector' .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean (inline proofs via FiniteDimensional.of_injective + Module.Basis.ext_multilinear in 3 branches)`
- `grep -n 'covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'abbrev Covector' Forms.lean`
- `grep -rn 'IsSeparable.exists_countable_dense_subset|IsSeparable.of_separableSpace|Countable.exists_eq_range|FiniteDimensional.proper_real|secondCountable_of_proper' Mathlib`
- `grep -rn 'measurable_find|preimage_find_eq_disjointed_setOf|StronglyMeasurable.of_discrete|comp_measurable|stronglyMeasurable_of_tendsto|StronglyMeasurable.piecewise' Mathlib/MeasureTheory Mathlib/Order`
- `grep -rn 'theorem of_injective|Module.Basis.ext_multilinear|measurableSet_lt|ae_eq_mk|Continuous.comp_stronglyMeasurable|mem_closure_iff|isOpen_lt' Mathlib`
- `lake env lean /tmp/near-max-split/Check.lean (assembly from stubs), Check2.lean, Check3.lean (full child proofs + assembly; #print axioms)`
- `independent reviewer: lake env lean /tmp/near-max-split/review/R1_Elab.lean, R2_Assembly.lean, R3_Children.lean, R4_Combined.lean, R5_Dbg.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-near-fa6e8571df/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-near-fa6e8571df/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/2e91ede8a686cf276482/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/5a60867de71e532024b6/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Closure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/tmp/near-max-split/Check3.lean`
- `/tmp/near-max-split/review/R4_Combined.lean`

Checks on the snapshot and workspace:
- The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean.
- No comparator-accepted declaration with either child type exists to reuse. The only related reserved node is imsupp_covector_finiteDimensional (∀ P n, FiniteDimensional ℝ (Covector (Euclid P) n)), which is still decomposing in another branch; its content is folded into child 1, not duplicated.
- Neither proposed name occurs in dag.json, in any of the 125 worktree Submissions, or in the contract.

SimonGMT Chapter06 supplies Covector (Forms.lean) and covectorEuclideanNorm with covectorEuclideanNorm_zero (Mass.lean).

The pinned Mathlib supplies:
- FiniteDimensional.of_injective and Module.Basis.ext_multilinear.
- FiniteDimensional.proper_real and secondCountable_of_proper.
- TopologicalSpace.IsSeparable.of_separableSpace and IsSeparable.exists_countable_dense_subset.
- Set.Countable.exists_eq_range, measurable_find (with preimage_find_eq_disjointed_setOf), StronglyMeasurable.of_discrete and StronglyMeasurable.comp_measurable.
- For the assembly: Continuous.comp_stronglyMeasurable, measurableSet_lt, AEStronglyMeasurable.ae_eq_mk, isOpen_lt and mem_closure_iff.

Mathlib has no global FiniteDimensional instance for Covector (Euclid P) n (#synth fails), so it is proved locally.

Both child types elaborate after import GMT.Ch07.Submission in the contract namespace and opens. The closure uses ContinuousAlternatingMap's topology, which is defeq to the normed topology. Measurability uses the Borel σ-algebra on Euclid P.

The selected frozen type compiles from sorry-stubbed children. Full proofs of both children plus the assembly compile with axioms [propext, Classical.choice, Quot.sound], in both the author file and the independent reviewer's files.
