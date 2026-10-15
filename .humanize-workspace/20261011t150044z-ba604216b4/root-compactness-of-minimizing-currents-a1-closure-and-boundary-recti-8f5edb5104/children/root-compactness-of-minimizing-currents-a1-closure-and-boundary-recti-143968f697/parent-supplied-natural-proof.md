# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1.norm_compare-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1 (coordinate bound) and 4 (finite dimension and norm comparison). Definiteness (step 2) is supplied by the sibling coord_definite and finite dimensionality by the sibling finite_dim.

Notation:
- V := Covector (Euclid P) n with its operator norm ‖·‖ (the ContinuousAlternatingMap norm).
- e_1, …, e_P is the standard orthonormal basis of ℝ^P (EuclideanSpace.basisFun (Fin P) ℝ). For J : Fin n → Fin P, e_J := (e_{J(i)})_{i ∈ Fin n}.
- |α| := covectorEuclideanNorm α = √(S(α)), where S(α) := Σ_{J : Fin n → Fin P} s_J(α), s_J(α) := α(e_J)² if J is strictly increasing and s_J(α) := 0 otherwise.
- Every s_J(α) ≥ 0, and |α| ≥ 0 (covectorEuclideanNorm_nonneg).

1. Coordinate bound. Let I be strictly increasing.
   - All summands are nonnegative, so the single summand s_I(α) = α(e_I)² is at most S(α) (Finset.single_le_sum).
   - Hence |α(e_I)| = √(α(e_I)²) ≤ √(S(α)) = |α| (Real.sqrt_sq_eq_abs, Real.sqrt_le_sqrt).

2. Coordinate map. Define L : V → ((Fin n → Fin P) → ℝ) by (Lα)(I) := α(e_I) if I is strictly increasing and (Lα)(I) := 0 otherwise. Evaluation at a fixed tuple is linear in α ((α + β)(v) = α(v) + β(v), (cα)(v) = c·α(v)). So every coordinate of L is linear (split on whether I is strictly increasing), and L is ℝ-linear.

3. Trivial kernel. If Lα = 0, then α(e_I) = (Lα)(I) = 0 for every strictly increasing I. By the sibling coord_definite, α = 0. Hence ker L = ⊥.

4. Antilipschitz bound.
   - V is finite-dimensional by the sibling finite_dim.
   - A linear map with trivial kernel on a finite-dimensional normed space is antilipschitz (LinearMap.exists_antilipschitzWith). So there is K > 0 (a positive element of ℝ≥0) with dist(α, β) ≤ K·dist(Lα, Lβ) for all α, β ∈ V.
   - Take β = 0 and use L0 = 0: ‖α‖ ≤ K·‖Lα‖ for every α (AntilipschitzWith.le_mul_dist, dist_zero_right).

5. Sup-norm estimate. The codomain (Fin n → Fin P) → ℝ carries the sup norm. For every I, |(Lα)(I)| ≤ |α|:
   - if I is strictly increasing, this is step 1;
   - otherwise (Lα)(I) = 0 ≤ |α|.
   Since |α| ≥ 0, this gives ‖Lα‖ ≤ |α| (pi_norm_le_iff_of_nonneg).

6. Conclusion. For every α ∈ V, ‖α‖ ≤ K·‖Lα‖ ≤ K·|α|, using step 4 and step 5 multiplied by K ≥ 0. The real number K is positive, which proves the claim. ∎

Lean outline (compiled against the frozen contract, a single theorem):
1. `intro P n; classical`
2. `have := Submission.dor_ims_lusin_covector_finiteDimensional P n`
3. Define `L` as a `LinearMap` with `toFun := fun α I => if StrictMono I then α (fun i => e (I i)) else 0`, where `e := EuclideanSpace.basisFun (Fin P) ℝ`. Prove both linearity fields by `funext I; by_cases hI : StrictMono I <;> simp [hI]`.
4. For `LinearMap.ker L = ⊥`, use `LinearMap.ker_eq_bot'` and `Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords P n α`.
5. `obtain ⟨K, hKpos, hK⟩ := L.exists_antilipschitzWith hker`, then `hK.le_mul_dist α 0` with `simp only [dist_zero_right, map_zero]`.
6. For the coordinate bound, apply `Finset.single_le_sum` to the summand function from the definition of covectorEuclideanNorm, then `rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt _`.
7. Conclude with `pi_norm_le_iff_of_nonneg (covectorEuclideanNorm_nonneg α)` and `gcongr`.

## Key steps

1. Coordinate bound: |α(e_I)| ≤ |α| for strictly increasing I (single summand ≤ sum; monotone square root).
2. The coordinate map L(α) = (α(e_I) if I strictly increasing, else 0)_I is ℝ-linear, and ker L = ⊥ by coord_definite.
3. V is finite-dimensional (finite_dim), so L is antilipschitz: ‖α‖ ≤ K‖Lα‖ with K > 0.
4. ‖Lα‖ ≤ |α| coordinatewise in the sup norm, hence ‖α‖ ≤ K|α|.

## Reference use

### local-project

Queries:
- `cat <run>/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical); cmp snapshot Mathlib LinearAlgebra/Alternating/Basic, Topology/Algebra/Module/Alternating/Basic, Data/Fin/Tuple/Sort, Analysis/Normed/Module/FiniteDimension, Topology/Order/Compact and Topology/MetricSpace/Lipschitz against lake-packages-25730c7c/mathlib (identical)`
- `grep -n in snapshot Mathlib for: 'theorem map_perm', 'map_eq_zero_of_not_injective', 'theorem toAlternatingMap_injective', 'coe_toAlternatingMap', 'ext_alternating', 'theorem monotone_sort', 'def sort', 'exists_antilipschitzWith', 'proper_real', 'theorem IsCompact.sSup_mem', 'of_le_add_mul', 'pi_norm_le_iff_of_nonneg', 'isCompact_of_isClosed_isBounded', 'units_eq_one_or'. Absent: ContinuousAlternatingMap.map_perm and ContinuousAlternatingMap.zero_apply (use toAlternatingMap.map_perm and `show … = (0 : ℝ)`)`
- `sed of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (def covectorEuclideanNorm, covectorEuclideanNorm_zero/_nonneg/_neg) and Forms.lean (abbrev Covector)`
- `python3 -I scans of dag.json covering: the selected node (depth 5, decomposing) and its siblings; accepted nodes whose lean_statement mentions covectorEuclideanNorm, FiniteDimensional or 'StrictMono I →'; status, candidate_commit and exact lean_statement of dor_ims_lusin_covector_finiteDimensional, rsd_mw_tfa_norm_props, cmr_covector_euclidean_equiv and dor_ims_sua_coeff_norm_rep; cross-parent reuse edges (554) and fresh-to-reused dependency edges (441)`
- `git diff b4d606db1 c9c005d1f0bc7c9b936d9d01037d132158020f22 and b4d606db1 f492ba4a003c8f1324077e050d48667ae23c7100 -- GMT/Ch07/Submission.lean (accepted Lean proofs of the two reused declarations); sed of their parent-supplied-natural-proof.md and of cmr_covector_euclidean_equiv's`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py for: _decompose depth gate node.depth >= max_depth, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _accepted_checkpoint, _reference_use_problem. Also store.py ensure and decomposition_scope.py`
- `python3 -I verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') gives the replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (...); noncomputable section; end`
- `python3 -I /tmp/dn-decomp-c55/py/gen_checks.py: flow lean_contract.validate_lean_statement passes on all four child types, and the parent lean_statement equals the DAG's. Fresh names cbr_ci_dr_dn_*: 0 DAG matches. Reused names: accepted, candidate_commit set, byte-identical lean_statement`
- `lake env lean /tmp/dn-decomp-c55/lean/{Types,Assembly,Probe,Full}.lean from the workspace root. Full.lean #print axioms for the parent and both fresh children = [propext, Classical.choice, Quot.sound]. Probe: ‖α‖ uses ContinuousAlternatingMap.instNormedAddCommGroup (operator norm)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Int/Associated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8f5edb5104/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8f5edb5104/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-c-16606b9c1a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-cov-64249b6f60/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dn-decomp-c55/lean/Full.lean`
- `/tmp/dn-decomp-c55/lean/Types.lean`
- `/tmp/dn-decomp-c55/lean/Assembly.lean`
- `/tmp/dn-decomp-c55/lean/Probe.lean`
- `/tmp/dn-decomp-c55/py/gen_checks.py`
- `/tmp/dn-decomp-c55/py/make_decomp.py`

Snapshot (project b4d606db, Mathlib 25730c7c): its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and the cited Mathlib files match the build packages.

Every lemma used by the child proofs and the parent assembly exists there, including:
- Module.Basis.ext_alternating, ContinuousAlternatingMap.toAlternatingMap_injective, AlternatingMap.map_perm
- Tuple.sort, Tuple.monotone_sort, Monotone.strictMono_of_injective, Int.units_eq_one_or
- LinearMap.exists_antilipschitzWith, pi_norm_le_iff_of_nonneg, FiniteDimensional.proper_real
- Metric.isCompact_of_isClosed_isBounded, IsCompact.sSup_mem, LipschitzWith.of_le_add_mul

Mathlib has no FiniteDimensional instance for continuous alternating maps. The DAG has two accepted checkpoints whose frozen types are byte-identical to children of this split, so both are reused:
- dor_ims_lusin_covector_finiteDimensional (finite dimension)
- rsd_mw_tfa_norm_props (triangle inequality, homogeneity, |α| ≤ C‖α‖, continuity)

No accepted declaration has the type of the definiteness or lower-bound child. cmr_covector_euclidean_equiv implies them, but via the Gram-determinant bound covectorEuclideanNorm_gram_bounds rather than the supplied sorting argument, so it is not used. The two fresh names are unused in the DAG.

All four child types elaborate in the exact comparator scope and pass validate_lean_statement. Complete single-theorem Lean proofs of both fresh children, and of the exact parent type from the four children, compile with axioms [propext, Classical.choice, Quot.sound].
