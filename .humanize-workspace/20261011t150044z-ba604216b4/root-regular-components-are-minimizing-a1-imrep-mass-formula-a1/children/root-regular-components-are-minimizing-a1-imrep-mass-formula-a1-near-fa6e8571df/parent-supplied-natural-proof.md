# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3.1 of the parent node's supplied proof of the mass formula M_W(T) = R.measure W (countable dense subset of B_E and the disjointified sets A_k), stated for a general measure and without the cutoff to K (the cutoff to K is applied by the caller). Notation (shared with the parent proof): ℝ^P = Euclid P = EuclideanSpace ℝ (Fin P) with standard orthonormal basis e_i = EuclideanSpace.basisFun (Fin P) ℝ i; Λ^n = Covector (Euclid P) n, the continuous alternating n-linear forms on ℝ^P; for a family b : Fin P → ℝ^P and j : Fin n → Fin P write b∘j := (b_{j(0)}, …, b_{j(n−1)}); |α|_E := covectorEuclideanNorm α = √(Σ_{I : Fin n → Fin P} [I strictly increasing] α(e∘I)²) (SimonGMT Chapter06/Mass.lean).

1. (Λ^n is finite dimensional and separable.) The linear map ev : Λ^n → ((Fin n → Fin P) → ℝ), α ↦ (j ↦ α(e∘j)) is injective: if all α(e∘j) vanish, the multilinear map underlying α vanishes on all tuples of basis vectors and hence is 0 (Module.Basis.ext_alternating, or Module.Basis.ext_multilinear with the standard basis in every slot). By Module.Finite.of_injective, Λ^n is finite dimensional over ℝ (Mathlib has no global instance FiniteDimensional ℝ (Covector (Euclid P) n); establish it locally). A finite-dimensional real normed space is proper (FiniteDimensional.proper_real), hence second countable and separable.

2. (Countable dense subset of the unit ball.) |·|_E is continuous on Λ^n (square root of a finite sum of squares of the continuous linear functionals α ↦ α(e∘I)), so B := {β : |β|_E ≤ 1} is closed; it is nonempty since |0|_E = 0 (covectorEuclideanNorm_zero). As a subset of a separable metric space, B is separable (TopologicalSpace.IsSeparable.mono), so there is a countable D ⊆ B with B ⊆ closure D (TopologicalSpace.IsSeparable.exists_countable_dense_subset). D is nonempty (0 ∈ B ⊆ closure D); enumerate D = {β_k : k ∈ ℕ} (Set.Countable.exists_eq_range).

3. (Strongly measurable version.) Let ξ̃ := (AEStronglyMeasurable.mk) be strongly measurable with ξ = ξ̃ μ-a.e. For each k, x ↦ ξ̃(x)(β_k) is strongly measurable (evaluation at β_k is a continuous linear map on MultiVector P n), so A_k := {x : 1 − η < ξ̃(x)(β_k)} is a measurable set.

4. (Selection.) Put A'_k := A_k ∖ ⋃_{i<k} A_i (pairwise disjoint measurable sets with ⋃_k A'_k = ⋃_k A_k) and define g(x) := β_k if x ∈ A'_k, g(x) := 0 if x ∉ ⋃_k A_k. Then g(x) ∈ D ∪ {0} ⊆ B, so |g(x)|_E ≤ 1 for all x. g is strongly measurable: it is the pointwise limit of the simple functions g_N := Σ_{k<N} A'_k.indicator (fun _ ↦ β_k) (for each x the sequence g_N(x) is eventually constant, equal to g(x)); use stronglyMeasurable_of_tendsto (or define g with Nat.find on the measurable predicate and prove strong measurability piecewise).

5. (Near-maximality.) For μ-a.e. x we have ξ(x) = ξ̃(x) and some β ∈ B with ξ(x)(β) = 1. The set {β' ∈ Λ^n : 1 − η < ξ(x)(β')} is open (ξ(x) is continuous) and contains β ∈ B ⊆ closure D, so it contains some β_k; thus x ∈ A_k ⊆ ⋃_i A_i. Let k' be the least index with x ∈ A_{k'}; then x ∈ A'_{k'}, g(x) = β_{k'} and ξ(x)(g(x)) = ξ̃(x)(β_{k'}) > 1 − η. Hence 1 − η ≤ ξ(x)(g(x)) for μ-a.e. x. ∎

## Key steps

1. Λ^n is finite dimensional (injective coefficient map), hence separable; the closed unit ball B of |·|_E has a countable dense subset {β_k}.
2. Replace ξ by a strongly measurable version ξ̃; the sets A_k = {1 − η < ξ̃(x)(β_k)} are measurable.
3. g := β_k on A'_k = A_k ∖ ⋃_{i<k} A_i (0 elsewhere) is strongly measurable with |g|_E ≤ 1.
4. By density and continuity of ξ(x), a.e. x lies in some A_k, so ξ(x)(g(x)) > 1 − η a.e.

## Reference use

### local-project

Queries:
- `cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 -I scan of dag.json (132 nodes) for lean_name collisions with the eight proposed regcomp_ names (none) and for related nodes (dtc_mass_eq_measure, rsd_massOn_eq_measure, dor_imrep_massOn_eq_measure_and_support, imrep_represents_massOn_eq_measure, covectorEuclideanNorm_gram_bounds: all still decomposing, with different types)`
- `git worktree list; grep -nE '^(theorem|lemma|def) ' .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no regcomp_ declarations)`
- `grep -n 'covectorEuclideanNorm|massAdmissibleOn|GeometricCurrentOn.massOn|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep -n 'wedgeCovectors|wedgeCovectors_apply_det|euclideanCovectorCoordinate' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `grep -n 'IsTestForm|testFormOnSubmodule|TestFormOn|GeometricCurrentOn' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean Currents.lean`
- `grep -rn 'exists_orthonormalBasis_extension_of_card_eq|sum_sq_inner_right|sum_inner_mul_inner' Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `grep -rn 'Integrable.exists_hasCompactSupport_lintegral_sub_le|MemLp.exists_hasCompactSupport_eLpNorm_sub_le|MemLp.exist_eLpNorm_sub_le' Mathlib`
- `grep -rn 'dist_normed_convolution_le|contDiff_convolution_left|support_convolution_subset|convolution_def|Continuous.exists_contDiff_approx|UniformContinuous.exists_contDiff_dist_le' Mathlib`
- `grep -n 'Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure' Mathlib/MeasureTheory/Measure/Regular.lean`
- `grep -rn 'map_eq_zero_of_not_injective|theorem map_perm|theorem Module.Basis.ext_multilinear|theorem det_permutation|def sort|monotone_sort' Mathlib`
- `grep -rn 'IsSeparable.exists_countable_dense_subset|IsSeparable.mono|exists_compact_between|IsOpen.exists_iUnion_isClosed|exists_cthickening_subset_open|exists_continuous_one_zero_of_isCompact|uniformContinuous_of_continuous' Mathlib`
- `grep -rn 'enorm_integral_le_lintegral_enorm|theorem withDensity_apply|lintegral_withDensity_eq_lintegral_mul₀' Mathlib/MeasureTheory`
- `lake env lean /tmp/imrep-mass-split/Inst.lean and Inst2.lean (#synth FiniteDimensional ℝ (Covector (Euclid P) n): fails; SeparableSpace: fails; CompleteSpace: found; ν.Regular for finite ν: found; signatures of the cited lemmas)`
- `lake env lean /tmp/imrep-mass-split/CheckFinal2.lean (eight frozen child types + le_antisymm parent assembly; #print axioms)`
- `lake env lean /tmp/imrep-mass-split/Check2.lean, Check3.lean, Check4.lean (unit_orientation_pairing from stubs; full proof of mass_le_measure; skeleton of measure_le_mass)`
- `python3 -I /tmp/imrep-mass-split/scripts/numcheck2.py (numeric check of the three covector facts for (P,n) in {(4,2),(5,3),(3,3),(4,1),(3,0),(2,3)})`
- `sed -n 755,770p book/chapter-06.txt (Remark 3.2(3))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Permutation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/imrep-mass-split/CheckFinal2.lean`
- `/tmp/imrep-mass-split/Check2.lean`
- `/tmp/imrep-mass-split/Check3.lean`
- `/tmp/imrep-mass-split/Check4.lean`
- `/tmp/imrep-mass-split/Inst.lean`
- `/tmp/imrep-mass-split/Inst2.lean`
- `/tmp/imrep-mass-split/scripts/numcheck2.py`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean. None of the eight proposed regcomp_ names occurs in dag.json or in any speculative Submission. No comparator-accepted declaration with an identical type exists to reuse: the related nodes dtc_mass_eq_measure, rsd_massOn_eq_measure, dor_imrep_massOn_eq_measure_and_support, imrep_represents_massOn_eq_measure and covectorEuclideanNorm_gram_bounds are all still decomposing and have different types.

SimonGMT Chapter06 provides covectorEuclideanNorm (with _zero, _neg, _nonneg), massAdmissibleOn, GeometricCurrentOn.massOn and le_massOn (Mass.lean), and wedgeCovectors with wedgeCovectors_apply_det (FormsDuality.lean). FormsDuality is not in the import closure of GMT.Ch07.Submission; the covector_norming child carries an import note.

Mathlib supplies: orthonormal-basis extension and Parseval (PiL2); C_c-density in L¹ for regular measures (ContinuousMapDense, not imported by the contract); regularity of finite Borel measures on Euclid P (Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure, which resolves); bump-function convolution (contDiff_convolution_left, dist_normed_convolution_le, support_convolution_subset); Continuous.exists_contDiff_approx; alternating-map lemmas (map_perm, map_eq_zero_of_not_injective, Basis.ext_multilinear/ext_alternating); Tuple.sort; Matrix.det_permutation; separability and exhaustion lemmas; and enorm_integral_le_lintegral_enorm, withDensity_apply, lintegral_withDensity_eq_lintegral_mul₀.

Mathlib has no FiniteDimensional or SeparableSpace instance for Covector (Euclid P) n (#synth fails), so near_maximizer proves finite-dimensionality locally; CompleteSpace and NormedSpace are found.

Verification:
- All eight frozen child types elaborate after import GMT.Ch07.Submission in the contract's namespace and opens.
- The le_antisymm assembly of regcomp_imrep_mass_formula compiles, using only propext, Classical.choice and Quot.sound, plus sorryAx from the child stubs.
- unit_orientation_pairing was proved from stubs of its two dependencies, and mass_le_measure was proved completely from unit_orientation_pairing.
- A skeleton of measure_le_mass applying near_maximizer and smooth_form_approx typechecks.
- A pure-Python check confirmed covector_sq_sum, covector_eval_le and covector_norming numerically, including n = 0, n = P and n > P.
- An independent reviewer subagent re-ran these checks and accepted the split.
