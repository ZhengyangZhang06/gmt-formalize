# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1.first_hit_selection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent node's supplied proof of regcomp_covector_field_near_maximizer (disjointified sets A'_k := A_k ∖ ⋃_{i<k} A_i, with g := β_k on A'_k and g := 0 off ⋃_k A_k). It is carried out by the 'Nat.find on the measurable predicate' route named there, for arbitrary measurable sets A_k and an arbitrary sequence b_k.

Notation: ℝ^P = Euclid P with its Borel σ-algebra (the instance on EuclideanSpace ℝ (Fin P)); Λ^n = Covector (Euclid P) n with its canonical normed topology. Classical logic is used throughout (membership is decided by classical choice). Fix P, n, A, b and hA : ∀ k, MeasurableSet (A k).

1. (Augmented family.) Define C : ℕ → Set (Euclid P) by C 0 := (⋃_k A k)ᶜ and C (k+1) := A k. Every C N is measurable: C 0 is the complement of a countable union of measurable sets (MeasurableSet.iUnion, MeasurableSet.compl), and C (k+1) = A k is measurable by hA.
   In Lean, define C (and b' in step 4) by pattern matching (`fun N => match N with | 0 => … | k + 1 => …`) or introduce it via `obtain ⟨C, hC⟩ : ∃ C, C = …`. Do not use a `let` built with `Nat.casesOn`: it leaves the DecidablePred instance needed by Nat.find stuck.

2. (The family covers ℝ^P.) For every x there is N with x ∈ C N: if x ∈ A k for some k, take N := k+1; otherwise x ∉ ⋃_k A k, i.e. x ∈ C 0.

3. (Measurable first-hit index.) For each x let N(x) := Nat.find (∃ N, x ∈ C N), the least N with x ∈ C N; it exists by step 2. The map N : Euclid P → ℕ is measurable by measurable_find, applied to the predicate p x N :⟺ x ∈ C N, whose sets {x | p x N} = C N are measurable by step 1. Concretely, {x | N(x) = j} = C j ∖ ⋃_{i<j} C i is measurable for every j (preimage_find_eq_disjointed_setOf and MeasurableSet.disjointed), and a map into ℕ with measurable fibres is measurable.

4. (Definition of g; strong measurability.) Let b' : ℕ → Λ^n be given by b' 0 := 0 and b' (k+1) := b k, and set g := b' ∘ N, i.e. g x := b' (N(x)). Since ℕ is countable with measurable singletons, every function on ℕ, in particular b', is strongly measurable (StronglyMeasurable.of_discrete). The composite of a strongly measurable function with a measurable map is strongly measurable (StronglyMeasurable.comp_measurable). Hence g is strongly measurable.
   For orientation: N(x) = k+1 ⟺ x ∈ A k ∖ ⋃_{i<k} A i = A'_k, and N(x) = 0 ⟺ x ∉ ⋃_k A k. So g = b k on A'_k and g = 0 off ⋃_k A k, which is the parent's construction.

5. (The pointwise alternative.) Fix x and put N := N(x); by Nat.find_spec, x ∈ C N.
   - If N = 0, then g x = b' 0 = 0 and x ∈ (⋃_k A k)ᶜ, so x ∉ A k for every k (otherwise x ∈ ⋃_k A k). The first alternative, g x = 0 ∧ ∀ k, x ∉ A k, holds.
   - If N = k+1, then g x = b' (k+1) = b k and x ∈ C (k+1) = A k. The second alternative holds with this k.
   In Lean: first `show` the goal with g x unfolded to b' (Nat.find (hC x)), then `generalize Nat.find (hC x) = N at` the membership fact and the goal, and do `cases N`. ∎

## Key steps

1. C 0 := (⋃_k A k)ᶜ and C (k+1) := A k (defined by match, not a Nat.casesOn let) are measurable and cover ℝ^P.
2. The first-hit index N(x) := Nat.find (∃ N, x ∈ C N) is measurable (measurable_find).
3. g := b' ∘ N with b' 0 = 0 and b' (k+1) = b k is strongly measurable (StronglyMeasurable.of_discrete composed via comp_measurable).
4. By Nat.find_spec: N(x) = 0 gives g x = 0 and x ∉ A k for all k; N(x) = k+1 gives g x = b k with x ∈ A k.

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
