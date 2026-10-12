# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1`
- Child DAG node: `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.finite_dirac_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the supplied proof of br_zero_dim_weak_limit_isIntegerMultiplicity (the finite integer Dirac sum is an integer multiplicity current), including the construction of the current. Zero coefficients are discarded inside the proof. U is an arbitrary subset of ℝ^P; openness is not used.

Conventions. ℝ^P := Eucl P, H⁰ := μHE[0], D⁰(U) := TestFormOn U 0. Every family Fin 0 → ℝ^P equals ![]. ε := simpleNVector (![] : Fin 0 → ℝ^P), so ε(α) = α(![]) for every 0-covector α (`simpleNVector_apply`).
(Lean note: do not `open scoped ContDiff`. Its `ω` notation clashes with the binder name ω of the frozen statement. Write the smoothness order as `((⊤ : ℕ∞) : WithTop ℕ∞)` if needed.)

Facts.
(F2) H⁰ = μH[0] (`Measure.euclideanHausdorffMeasure_zero`) and H⁰{x} = 1 (`Measure.hausdorffMeasure_zero_singleton`). Hence for a finite set F (a Finset) and any g : ℝ^P → ℝ:
 - g is H⁰-integrable on F, as F is a finite union of singletons of finite measure (`integrableOn_singleton`, `integrableOn_finite_biUnion`);
 - ∫_F g dH⁰ = Σ_{x∈F} H⁰.real{x}·g(x) = Σ_{x∈F} g(x) (`setIntegral_finset`).
(F5) For a 0-covector α, |α(![])| ≤ ‖α‖ (operator-norm bound; the empty product of norms is 1). For every f, ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ (`norm_iteratedFDeriv_zero`).

Proof.
1. (The functional.) For ω ∈ D⁰(U) put L(ω) := Σ_{x∈D} a(x)·ω(x)(![]). L is ℝ-linear: the coercion of TestFormOn U 0 to forms is linear ((ω + η)(x) = ω(x) + η(x), (tω)(x) = t·ω(x)), and evaluating a covector at ![] is linear.
2. (Sequential continuity.) Let (ω_j) be a sequence in D⁰(U) with TestFormOnConverges ω_j 0.
 Then there is a compact K ⊆ U with tsupport ω_j ⊆ K for all j, and (case k = 0) iteratedFDeriv ℝ 0 ω_j → iteratedFDeriv ℝ 0 0 = 0 uniformly on K. By (F5), sup_{y∈K} ‖ω_j(y)‖ → 0.
 Let x ∈ D:
 - if x ∈ K, then |ω_j(x)(![])| ≤ ‖ω_j(x)‖ → 0, by (F5);
 - if x ∉ K, then x ∉ tsupport ω_j, so ω_j(x) = 0 for all j.
 In both cases ω_j(x)(![]) → 0, hence L(ω_j) → 0 (a finite sum).
 Therefore Y := ⟨L, (this continuity)⟩ is an element of GeometricCurrentOn U 0 with Y(ω) = Σ_{x∈D} a(x)·ω(x)(![]) for every ω ∈ D⁰(U). It remains to show IsIntegerMultiplicity Y.
3. (The triple.) Let M := {x ∈ D : a(x) ≠ 0} (the coercion of the Finset D.filter (a · ≠ 0)) and S⁻ := {x ∈ D : a(x) < 0} (the coercion of D.filter (a · < 0)). Both are finite. Put θ(x) := |a(x)| (as a real number), and ξ(x) := −ε if x ∈ S⁻, ξ(x) := ε otherwise.
 Then θ(x) = (natAbs(a(x)) : ℝ) for every x, so θ(x) ∈ ℕ on M.
 Moreover, for x ∈ M and every 0-covector α, θ(x)·ξ(x)(α) = a(x)·α(![]):
 - if a(x) < 0, then x ∈ S⁻ and θ(x)·ξ(x)(α) = |a(x)|·(−α(![])) = a(x)·α(![]);
 - if a(x) > 0, then x ∉ S⁻ and θ(x)·ξ(x)(α) = |a(x)|·α(![]) = a(x)·α(![]).
4. (IsRectifiableTriple U 0 M θ ξ.)
 (a) subset: M ⊆ D ⊆ U.
 (b) nullMeasurableSet: M is finite, hence measurable (`Set.Finite.measurableSet`), hence null-measurable.
 (c) countablyRectifiable: take M₀ := ∅ (H⁰(∅) = 0). M is finite, hence countable, and ℝ^P is nonempty, so there is g : ℕ → ℝ^P with M ⊆ range g (`Set.countable_iff_exists_subset_range`; concretely, list the points of M and repeat 0 afterwards). Let F_j : Eucl 0 → ℝ^P be the constant map with value g(j). Constant maps are Lipschitz (constant 0), and range F_j = {g(j)} because Eucl 0 is nonempty. So M ⊆ range g = ⋃_j range F_j ⊆ ∅ ∪ ⋃_j range F_j.
 (d) pos: θ(x) = |a(x)| > 0 for x ∈ M.
 (e) integrableOn: for every K, M ∩ K is finite, and every real function is H⁰-integrable on a finite set by (F2).
 (f) aestronglyMeasurable: ξ is piecewise constant, ξ = (if x ∈ S⁻ then −ε else ε), and S⁻ is finite, hence measurable. So ξ is strongly measurable (`StronglyMeasurable.ite` / `stronglyMeasurable_const.piecewise`), in particular a.e. strongly measurable for H⁰⌞M. (This avoids building ξ as a finite sum of indicators in NVector; in this Lean environment instance search does not find `ContinuousAdd (NVector (Eucl P) 0)` directly.)
 (g) orients: since M is measurable, it suffices to prove the property for every x ∈ M (`ae_restrict_of_forall_mem`). Fix x ∈ M and take τ := ![] : Fin 0 → ℝ^P.
 - Orthonormal ℝ τ holds vacuously.
 - L := span ℝ (range τ) = span ℝ ∅ = ⊥, so (L : Set ℝ^P) = {0} and finrank L = 0.
 - By definition ξ(x) ∈ {ε, −ε}, and ε = simpleNVector τ, so ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ.
 It remains to prove HasWeightedApproximateTangentSpaceAt 0 M θ x L. The dimension condition finrank L = 0 holds. For f ∈ C_c(ℝ^P, ℝ), write η_r(y) := blowUpMap x r y = r⁻¹•(y − x) and F(r) := ∫_{η_r(M)} f(z)·θ(x + r•z) dH⁰(z); we must show F(r) → θ(x)·∫_L f dH⁰ as r → 0⁺.
 – Right side: ∫_{{0}} f dH⁰ = f(0) by (F2), so the target is θ(x)·f(0).
 – Choice of constants: tsupport f is compact, hence bounded, so there is R > 0 with f(z) = 0 whenever ‖z‖ > R. Let d := min{‖y − x‖ : y ∈ M, y ≠ x} if M ≠ {x}, and d := 1 otherwise; d > 0 since M is finite. Put r₀ := d/R > 0.
 – Let 0 < r < r₀. Then η_r(M) is the finite set {η_r(y) : y ∈ M} (the image of a Finset), η_r(x) = 0 ∈ η_r(M), and x + r•η_r(y) = y. If z ∈ η_r(M) and z ≠ 0, then z = η_r(y) with y ∈ M, y ≠ x, so ‖z‖ = ‖y − x‖/r ≥ d/r > R and f(z) = 0. By (F2), F(r) = Σ_{z∈η_r(M)} f(z)·θ(x + r•z) = f(0)·θ(x): only z = 0 contributes, and x + r•0 = x.
 – Thus F(r) = θ(x)·f(0) for all r ∈ (0, r₀), so F(r) → θ(x)·f(0) along 𝓝[>] 0 (the function is eventually constant).
 This completes IsRectifiableTriple U 0 M θ ξ.
5. (The action.) For ω ∈ D⁰(U):
 tauAction 0 M θ ξ ω = ∫_M θ(x)·ξ(x)(ω(x)) dH⁰
 = Σ_{x∈M} θ(x)·ξ(x)(ω(x)) (by (F2))
 = Σ_{x∈M} a(x)·ω(x)(![]) (step 3 with α = ω(x))
 = Σ_{x∈D} a(x)·ω(x)(![]) (the omitted terms have a(x) = 0)
 = Y(ω).
6. (Conclusion.) (M, θ, ξ) witnesses IsIntegerMultiplicity Y: the triple condition holds (step 4), θ(x) = natAbs(a(x)) ∈ ℕ on M (step 3), and Y(ω) = tauAction 0 M θ ξ ω for all ω (step 5). Together with step 2, Y is the required current. ∎

## Key steps

1. Define Y(ω) := Σ_{x∈D} a(x)ω(x)(![]). It is linear, and sequentially continuous because TestFormOnConverges at order 0 gives convergence at every point.
2. Triple: M := {x ∈ D : a(x) ≠ 0}, θ := |a|, and ξ := −ε on {a < 0}, ε elsewhere (ε = simpleNVector ![]). Then θξ(α) = a·α(![]) on M.
3. M is finite, so it is measurable and countably 0-rectifiable (constant maps), θ is integrable on it, and ξ is strongly measurable (piecewise constant).
4. Orientation at each x ∈ M uses the empty frame: for small r the blown-up set η_r(M) meets the support of f only at 0, so the weighted tangent space is {0}.
5. tauAction 0 M θ ξ ω = Σ_{x∈M} a(x)ω(x)(![]) = Y(ω).

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
