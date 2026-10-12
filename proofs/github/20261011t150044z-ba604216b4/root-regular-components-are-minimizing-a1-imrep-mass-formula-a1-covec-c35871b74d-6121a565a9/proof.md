# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_sq_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(i)–(ii) of the parent node's supplied proof of the mass formula M_W(T) = R.measure W (Simon Ch. 6, Remark 3.2(3), chapter-06.txt lines 763–766; coefficient norm of (6.1.5)/(6.1.15)). Notation (shared with the parent proof): ℝ^P = Euclid P = EuclideanSpace ℝ (Fin P) with standard orthonormal basis e_i = EuclideanSpace.basisFun (Fin P) ℝ i; Λ^n = Covector (Euclid P) n, the continuous alternating n-linear forms on ℝ^P; for a family b : Fin P → ℝ^P and j : Fin n → Fin P write b∘j := (b_{j(0)}, …, b_{j(n−1)}); |α|_E := covectorEuclideanNorm α = √(Σ_{I : Fin n → Fin P} [I strictly increasing] α(e∘I)²) (SimonGMT Chapter06/Mass.lean). For a family b put S_b(α) := Σ_{j : Fin n → Fin P} α(b∘j)². We must show S_f(α) = n!·|α|_E².

1. (Square of the norm.) The radicand Σ_I [I strictly increasing] α(e∘I)² is a finite sum of nonnegative terms, so |α|_E² = Σ_{I strictly increasing} α(e∘I)² (Real.sq_sqrt).

2. (Basis independence by slotwise Parseval.) Let b, b' be orthonormal bases of ℝ^P indexed by Fin P. For m = 0, 1, …, n put H_m := Σ_{j : Fin n → Fin P} α(w_m(j))², where w_m(j)(k) := b_{j(k)} if k < m and w_m(j)(k) := b'_{j(k)} if k ≥ m. Then H_0 = S_{b'}(α) and H_n = S_b(α). Fix m < n and split every j into its m-th value i := j(m) ∈ Fin P and its values j' on the other n − 1 slots (j ↦ (j(m), j') is a bijection, e.g. via Fin.insertNth / Fin.removeNth). For fixed j' the map λ_{j'}(v) := α(u_0, …, u_{m−1}, v, u_{m+1}, …, u_{n−1}), with u_k := b_{j(k)} for k < m and u_k := b'_{j(k)} for k > m, is a linear functional of v ∈ ℝ^P (α is multilinear). Writing λ_{j'}(v) = ⟨r, v⟩ with r := Σ_a λ_{j'}(e_a) e_a, Parseval for orthonormal bases (OrthonormalBasis.sum_sq_inner_right) gives Σ_i λ_{j'}(b_i)² = ‖r‖² = Σ_i λ_{j'}(b'_i)². The terms of H_{m+1} with fixed j' are exactly the λ_{j'}(b_i)² (i ∈ Fin P) and those of H_m are the λ_{j'}(b'_i)²; summing over j' gives H_{m+1} = H_m. By induction on m, S_b(α) = S_{b'}(α); in particular S_f(α) = S_e(α). (Equivalent implementation: expand b_i = Σ_a ⟨e_a, b_i⟩ e_a in every slot by multilinearity and use Σ_i ⟨e_a, b_i⟩⟨e_{a'}, b_i⟩ = δ_{aa'} (OrthonormalBasis.sum_inner_mul_inner) in each of the n slots; all cross terms cancel and S_b(α) = S_e(α).)

3. (Non-injective tuples.) If j is not injective then e∘j is not injective (e is injective), so α(e∘j) = 0 because α is alternating (ContinuousAlternatingMap.map_eq_zero_of_not_injective). Hence S_e(α) = Σ_{j injective} α(e∘j)².

4. (Injective tuples = increasing tuples × permutations.) Every injective j : Fin n → Fin P factors uniquely as j = I∘π with I : Fin n → Fin P strictly increasing and π ∈ Perm(Fin n). Existence: with σ := Tuple.sort j, j∘σ is monotone (Tuple.monotone_sort) and injective, hence strictly increasing; take I := j∘σ and π := σ⁻¹. Uniqueness: if I∘π = I'∘π' with I, I' strictly increasing, then I and I' have the same range, and a strictly increasing map Fin n → Fin P is determined by its range (it is the increasing enumeration of that n-element set, cf. StrictMono.range_inj_of_wellFoundedLT / Finset.orderEmbOfFin_unique), so I = I'; then π = π' because I is injective. Conversely each such I∘π is injective. Thus (I, π) ↦ I∘π is a bijection from {I strictly increasing} × Perm(Fin n) onto {j injective}.

5. (Signs.) For I strictly increasing and π ∈ Perm(Fin n), α(e∘I∘π) = sign(π)·α(e∘I) (AlternatingMap.map_perm applied to α.toAlternatingMap), so α(e∘(I∘π))² = α(e∘I)².

6. (Counting.) By steps 3–5, S_e(α) = Σ_{I strictly increasing} Σ_{π ∈ Perm(Fin n)} α(e∘I)² = |Perm(Fin n)|·Σ_{I strictly increasing} α(e∘I)² = n!·|α|_E² (Fintype.card_perm, Fintype.card_fin and step 1).

7. (Conclusion.) By steps 2 and 6, Σ_{j : Fin n → Fin P} α(f∘j)² = S_f(α) = S_e(α) = n!·|α|_E². The same argument covers n = 0 (one empty tuple, which is strictly increasing; 0! = 1) and n > P (no injective and no strictly increasing tuples; both sides are 0). ∎

## Key steps

1. |α|_E² equals the sum of α(e∘I)² over strictly increasing I.
2. Slotwise Parseval (hybrid sums H_m) shows Σ_j α(b∘j)² is the same for every orthonormal basis b.
3. Non-injective tuples contribute 0; injective tuples are exactly I∘π (I increasing, π a permutation) and contribute α(e∘I)² each.
4. Counting the n! permutations gives Σ_j α(e∘j)² = n!·|α|_E², hence Σ_j α(f∘j)² = n!·|α|_E².

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
