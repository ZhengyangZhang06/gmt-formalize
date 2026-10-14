# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1`
- Child DAG node: `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_repr-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1(a)–(c) of the supplied proof of br_zero_dim_weak_limit_isIntegerMultiplicity (structure of 0-dimensional integer multiplicity currents), with all details filled in. U is an arbitrary subset of ℝ^P; openness is not used.

Conventions. ℝ^P := Eucl P, H⁰ := μHE[0], D⁰(U) := TestFormOn U 0. Every family Fin 0 → ℝ^P equals ![]. For a 0-form ω put ω°(x) := ω(x)(![]). Let 𝟙 := ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) 1 (the 0-covector with value 1) and ε := simpleNVector (![] : Fin 0 → ℝ^P). Then ε(α) = α(![]) and ε(𝟙) = 1.

Facts.
(F1) Every 0-covector α satisfies α = α(![]) • 𝟙: both sides take the value α(![]) at the unique family ![]. Hence for every 0-vector w (a continuous linear functional on 0-covectors), w(α) = α(![])·w(𝟙).
(F2) H⁰ = μH[0] (Mathlib `Measure.euclideanHausdorffMeasure_zero`) and H⁰{x} = 1 for every x (`Measure.hausdorffMeasure_zero_singleton`). Consequently:
 (a) H⁰(F) = #F for every finite set F (finite additivity over measurable singletons, `sum_measure_singleton`);
 (b) if H⁰(E) = 0 then E = ∅ (if x ∈ E then 1 = H⁰{x} ≤ H⁰(E));
 (c) if H⁰(E) < ∞ then E is finite. If E were infinite, then for every n ∈ ℕ it would contain a finite subset F_n with #F_n = n (`Set.Infinite.exists_subset_card_eq`), so H⁰(E) ≥ n for all n, i.e. H⁰(E) = ∞;
 (d) for a finite set F (a Finset) and any g : ℝ^P → ℝ, g is H⁰-integrable on F, because F is a finite union of singletons of measure 1 (`integrableOn_singleton`, `integrableOn_finite_biUnion`); and ∫_F g dH⁰ = Σ_{x∈F} H⁰.real{x}·g(x) = Σ_{x∈F} g(x) (`setIntegral_finset`).
(F3) Every H⁰-null-measurable set M is measurable. NullMeasurableSet gives a measurable t with M =ᵐ[H⁰] t, i.e. H⁰((M \ t) ∪ (t \ M)) = 0. By (F2b), M \ t = t \ M = ∅, so M = t.

Proof.
1. (Unpacking.) Since Y is integer multiplicity, there are M ⊆ ℝ^P, θ : ℝ^P → ℝ and ξ : ℝ^P → NVector (Eucl P) 0 such that:
 - IsRectifiableTriple U 0 M θ ξ holds;
 - θ(x) = k_x for some k_x ∈ ℕ whenever x ∈ M;
 - Y(ω) = tauAction 0 M θ ξ ω = ∫_M θ(x)·ξ(x)(ω(x)) dH⁰(x) for every ω ∈ D⁰(U).
 Put N := M. The field `subset` gives N ⊆ U. By the field `nullMeasurableSet` and (F3), M is measurable.
2. (θ ≥ 1 on M.) For x ∈ M, θ(x) = k_x with k_x ∈ ℕ, and θ(x) > 0 by the field `pos`. Hence k_x ≥ 1 and θ(x) ≥ 1.
3. (Local finiteness, conclusion (i).) Let K ⊆ U be compact. By the field `integrableOn`, θ is H⁰-integrable on M ∩ K, so ∫⁻_{M∩K} ‖θ‖ₑ dH⁰ < ∞. The set M ∩ K is measurable (M by step 1; K is closed), and ‖θ(x)‖ₑ ≥ 1 for x ∈ M ∩ K by step 2. So H⁰(M ∩ K) = ∫⁻_{M∩K} 1 dH⁰ ≤ ∫⁻_{M∩K} ‖θ‖ₑ dH⁰ < ∞. By (F2c), M ∩ K = N ∩ K is finite.
4. (Orientation at every point of M.) Let B be the set of x ∈ ℝ^P for which there is no τ : Fin 0 → ℝ^P with Orthonormal ℝ τ, HasWeightedApproximateTangentSpaceAt 0 M θ x (span ℝ (range τ)) and (ξ(x) = simpleNVector τ ∨ ξ(x) = −simpleNVector τ).
 The field `orients` says exactly that (H⁰⌞M)(B) = 0. By `Measure.le_restrict_apply`, H⁰(B ∩ M) ≤ (H⁰⌞M)(B) = 0, so B ∩ M = ∅ by (F2b).
 Thus for every x ∈ M there is τ : Fin 0 → ℝ^P with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ. Since τ = ![], ξ(x) = σ_x·ε with σ_x ∈ {1, −1}, and ξ(x)(𝟙) = σ_x·𝟙(![]) = σ_x.
5. (Coefficients, conclusion (ii).) Define c(x) := ⌊θ(x)·ξ(x)(𝟙)⌋ ∈ ℤ for every x ∈ ℝ^P. For x ∈ M, θ(x)·ξ(x)(𝟙) = σ_x·k_x is an integer by steps 1 and 4, so c(x) = σ_x·k_x. In particular (c(x) : ℝ) = θ(x)·ξ(x)(𝟙), and |c(x)| = k_x ≥ 1, so c(x) ≠ 0.
6. (The integrand.) Fix ω ∈ D⁰(U) and put g(x) := θ(x)·ξ(x)(ω(x)).
 - By (F1), ξ(x)(ω(x)) = ω°(x)·ξ(x)(𝟙). So for x ∈ M, step 5 gives g(x) = θ(x)ξ(x)(𝟙)·ω°(x) = c(x)·ω°(x).
 - For x ∉ tsupport ω we have ω(x) = 0, hence g(x) = 0 and ω°(x) = 0.
7. (Reduction of the integral to a finite sum.) Since ω has compact support and tsupport ω ⊆ U (ω ∈ D⁰(U)), tsupport ω is a compact subset of U. So S₀ := M ∩ tsupport ω is finite by step 3, and it is measurable.
 The functions 1_M·g and 1_{S₀}·g coincide everywhere: they can only differ at points of M \ tsupport ω, where g = 0 by step 6. Since M and S₀ are measurable, `integral_indicator` gives ∫_M g dH⁰ = ∫ 1_M·g dH⁰ = ∫ 1_{S₀}·g dH⁰ = ∫_{S₀} g dH⁰. By (F2d), ∫_{S₀} g dH⁰ = Σ_{x∈S₀} g(x).
8. (The finsum.) The function x ↦ (c(x)·ω°(x) if x ∈ M, 0 otherwise) vanishes outside S₀ by step 6. Hence ∑ᶠ_{x∈M} c(x)·ω°(x) = Σ_{x∈S₀} c(x)·ω°(x). (A finsum over a set equals the finite sum over any finite subset containing all points of the set where the summand is nonzero: `finsum_mem_eq_sum_of_subset` or `finsum_mem_eq_sum_of_inter_support_eq`, the additive forms of `finprod_mem_eq_prod_of_subset` / `finprod_mem_eq_prod_of_inter_mulSupport_eq`.)
9. (Conclusion (iii).) By step 6, Σ_{x∈S₀} g(x) = Σ_{x∈S₀} c(x)·ω°(x). Combining steps 1, 7 and 8: Y(ω) = ∫_M g dH⁰ = Σ_{x∈S₀} c(x)·ω°(x) = ∑ᶠ_{x∈N} (c(x) : ℝ)·ω(x)(![]). Together with N ⊆ U (step 1), (i) (step 3) and (ii) (step 5), this proves the lemma. ∎

## Key steps

1. Unpack Y = τ(M, θ, ξ) and take N := M ⊆ U. M is H⁰-measurable because H⁰ is counting measure, so H⁰-null sets are empty.
2. θ ≥ 1 on M and θ integrable on M ∩ K give H⁰(M ∩ K) < ∞, so M ∩ K is finite.
3. The orientation property holds at every point of M, so ξ(x) = ±simpleNVector ![]. Set c(x) := ⌊θ(x)·ξ(x)(𝟙)⌋ = ±θ(x) ∈ ℤ∖{0}.
4. Every 0-covector equals α(![])•𝟙, so θ(x)ξ(x)(ω(x)) = c(x)ω(x)(![]) on M, and the integrand vanishes off tsupport ω.
5. The integral over M reduces to the finite sum over M ∩ tsupport ω, which equals the finsum ∑ᶠ_{x∈N} c(x)ω(x)(![]).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean <workspace>/GMT/Ch06/Submission.lean (identical)`
- `rg -n 'theorem euclideanHausdorffMeasure_zero|def euclideanHausdorffMeasure|notation.*μHE' mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_zero_singleton' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem setIntegral_finset|theorem integral_fintype|theorem integral_countable' mathlib/Mathlib/MeasureTheory`
- `rg -n 'sum_measure_singleton|measure_biUnion_finset' mathlib/Mathlib/MeasureTheory/Measure/*.lean`
- `rg -n 'theorem le_restrict_apply' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'integrableOn_singleton|integrableOn_finite_biUnion|integrableOn_finset_iUnion' mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `rg -n 'theorem IsCompact.tendsto_subseq' mathlib/Mathlib/Topology/Sequences.lean`
- `rg -n 'structure ContDiffBump|theorem one_of_mem_closedBall|theorem tsupport_eq' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n 'theorem closure_ball|theorem isCompact_closedBall' mathlib/Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean`
- `rg -n 'def constOfIsEmpty' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `rg -n 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -n 'finprod_mem_eq_prod_of_subset|finprod_mem_eq_prod_of_inter_mulSupport_eq' mathlib/Mathlib/Algebra/BigOperators/Finprod.lean`
- `grep -rn 'theorem norm_iteratedFDeriv_zero' mathlib/Mathlib/Analysis/Calculus/ContDiff`
- `grep -n 'theorem countable_iff_exists_subset_range' mathlib/Mathlib/Data/Set/Countable.lean`
- `inspect simongmt Chapter06/{Currents,Mass,Forms,FormsDuality,CurrentLocalEquality}.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, TestFormOnConverges, WeaklyConvergesOn, massOn, massAdmissibleOn, le_massOn, covectorEuclideanNorm, simpleNVector, HasWeightedApproximateTangentSpaceAt, blowUpMap, CountablyRectifiable)`
- `python3 scan of dag.json (sibling br_isIntegerMultiplicity_of_local frozen statement; no br_zd_* lean_name reserved; new node root.integrality_weak_limits-a1.zero_dim-a1 with identical type)`
- `lake build GMT.Ch06.Submission (scratch /tmp/zd_decomp from git archive d8d46c9, pinned packages)`
- `lake env lean Scratch/Facts.lean, Scratch/Assembly.lean, Scratch/Combined.lean and NodeChallenge modules generated by gmt-compare.py child_modules after lean_contract.validate_lean_statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/BigOperators/Finprod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-zero-dim-a1/parent-child-handoff.json`
- `/tmp/zd_decomp/Scratch/Facts.lean`
- `/tmp/zd_decomp/Scratch/Assembly.lean`
- `/tmp/zd_decomp/Scratch/Combined.lean`
- `/tmp/zd_lean_A/Scratch/ChildA.lean`
- `/tmp/zd_lean_B/Scratch/ChildB.lean`
- `/tmp/zd_lean_C/Scratch/ChildC.lean`
- `/tmp/zd_lean_D/Scratch/ChildD.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Contract.lean is byte-identical to the frozen Submission.lean.

The Mathlib and SimonGMT facts the children need are all present:
- H⁰ = μHE[0] = μH[0] (euclideanHausdorffMeasure_zero), with H⁰{x} = 1 (hausdorffMeasure_zero_singleton) and sum_measure_singleton;
- set integrals over a Finset are finite sums (setIntegral_finset, integrableOn_singleton, integrableOn_finite_biUnion);
- le_restrict_apply, IsCompact.tendsto_subseq and isCompact_univ_pi;
- ContDiffBump (one_of_mem_closedBall, tsupport_eq), closure_ball and isCompact_closedBall;
- ContinuousAlternatingMap.constOfIsEmpty and the finprod/finsum subset lemmas;
- norm_iteratedFDeriv_zero and countable_iff_exists_subset_range;
- SimonGMT's massOn/le_massOn, covectorEuclideanNorm, simpleNVector, blowUpMap and HasWeightedApproximateTangentSpaceAt.

The 0-dimensional conventions were checked in Lean: α = α(![]) • 𝟙, covectorEuclideanNorm α = |α(![])|, H⁰ of a Finset is its cardinality, finite H⁰ implies a finite set, H⁰-null implies empty, and the empty-frame facts.

All four child statements elaborate in the comparator's child scope. Each is fully proved in Lean with axioms [propext, Classical.choice, Quot.sound] only. The parent assembly typechecks from them plus the DAG sibling br_isIntegerMultiplicity_of_local; its only sorryAx comes from that sibling.

No br_zd_* name is reserved in the DAG. A separate DAG node, iwl_zero_dim_integrality, has the identical frozen type as this node.
