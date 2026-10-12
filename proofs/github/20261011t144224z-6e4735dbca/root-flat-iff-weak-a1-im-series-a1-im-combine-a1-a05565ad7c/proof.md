# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.im_combine-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is steps 5–9 of the supplied proof of Simon 3.13 for M-absolutely convergent series.

Notation:
- I := {r : c_r ≠ 0}; |c_r| := ((c_r).natAbs : ℝ≥0∞); s(τ) := simpleNVector τ.
- 'null' means H-null; hTL is the tangent-locality hypothesis.
- For x ∈ M_r, θ_r(x) ∈ ℕ and θ_r(x) > 0 (field pos), so θ_r(x) ≥ 1.

Lean note (checked at this pin): instance search finds no PseudoMetrizableSpace, MetrizableSpace or ContinuousAdd on `NVector (Eucl P) n`.
- A local PseudoMetrizableSpace instance compiles:
  `letI u : UniformSpace (NVector (Eucl P) n) := PseudoMetricSpace.toUniformSpace; haveI : (uniformity (NVector (Eucl P) n)).IsCountablyGenerated := @EMetric.instIsCountablyGeneratedUniformity _ PseudoMetricSpace.toPseudoEMetricSpace; exact @UniformSpace.pseudoMetrizableSpace _ u this`
- After that, MetrizableSpace is found by infer_instance, and aestronglyMeasurable_iUnion_iff, StronglyMeasurable.measurableSet_eq_fun and aestronglyMeasurable_of_tendsto_ae apply to NVector-valued maps.
- The construction below never adds NVector-valued functions. It only glues, restricts, multiplies by real functions (AEStronglyMeasurable.smul) and takes indicators (aestronglyMeasurable_indicator_iff₀); all of these work as is.

1. (Exceptional null sets.)
   (a) The sibling overlap_finite applies. Its hypotheses are the fields subset, nullMeasurableSet and integrableOn of the triples, θ_r ≥ 1 on M_r, and the summability hypothesis. It gives:
       - Θ := Σ'_r |c_r|·1_{M_r}·ofReal θ_r satisfies ∫⁻_K Θ dH < ∞ for every compact K ⊆ U;
       - there is a null set N_fin such that F(x) := {r ∈ I : x ∈ M_r} is finite for x ∉ N_fin.
   (b) For each r, the field orients and ae_restrict_iff'₀ (M_r null-measurable) give a null set N_r with the following property: for every x ∈ M_r ∖ N_r there is an orthonormal τ with HasWeightedApproximateTangentSpaceAt n M_r θ_r x (span(range τ)) and ξ_r(x) = ±s(τ).
   (c) For each r, r', hTL applied to (M_r, θ_r) and (M_{r'}, θ_{r'}) is exactly the locality hypothesis of the sibling orientation_sign. The hypotheses of hTL are the fields subset, nullMeasurableSet, pos and integrableOn of the two triples. orientation_sign then gives a null set N_{r,r'} with ξ_r(x) = ±ξ_{r'}(x) for x ∈ (M_r ∩ M_{r'}) ∖ N_{r,r'}.
   Let N₀ := toMeasurable H (N_fin ∪ ⋃_r N_r ∪ ⋃_{r,r'} N_{r,r'}). It is a measurable null set containing all of these, because countable unions of null sets are null. Put G := ℝ^P ∖ N₀; G is measurable and H(N₀) = 0.

2. (Union and first index.)
   - M_∪ := ⋃_{r∈I} M_r ⊆ U is null-measurable.
   - For x ∈ M_∪ let r(x) := min{r ∈ I : x ∈ M_r} (Nat.find).
   - For r ∈ I put A_r := M_r ∖ ⋃_{r'∈I, r'<r} M_{r'}, and A_r := ∅ for r ∉ I.
   - Then A_r = {x ∈ M_∪ : r(x) = r}, each A_r is null-measurable (a finite Boolean combination), and M_∪ = ⋃_r A_r.

3. (Reference orientation.)
   - Define ξ̂(x) := ξ_{r(x)}(x) for x ∈ M_∪ and ξ̂(x) := 0 otherwise. On A_r, ξ̂ = ξ_r.
   - ξ_r is a.e.-strongly measurable for H.restrict M_r, hence for H.restrict A_r (A_r ⊆ M_r).
   - Since ξ̂ = ξ_r on the null-measurable set A_r, ξ̂ is a.e.-strongly measurable for H.restrict A_r (AEStronglyMeasurable.congr with ae_restrict_mem₀).
   - By aestronglyMeasurable_iUnion_iff (countable cover M_∪ = ⋃_r A_r), ξ̂ is a.e.-strongly measurable for H.restrict M_∪.

4. (Signs.) For r ∈ ℕ and x ∈ ℝ^P let σ_r(x) := 1 if ξ_r(x) = ξ̂(x), and σ_r(x) := −1 otherwise.
   - Let r ∈ I and x ∈ G ∩ M_r. Then x ∈ M_∪, r(x) ∈ I and x ∈ (M_r ∩ M_{r(x)}) ∖ N_{r,r(x)}, so ξ_r(x) = ±ξ̂(x) by 1(c).
   - In both cases ξ_r(x) = σ_r(x)·ξ̂(x): if ξ_r(x) ≠ ξ̂(x), then ξ_r(x) = −ξ̂(x) and σ_r(x) = −1.
   - Measurability: for r ∈ I, ξ_r and ξ̂ are a.e.-strongly measurable for H.restrict M_r (as M_r ⊆ M_∪). Replacing them by strongly measurable versions changes {ξ_r = ξ̂} only by a null set, and the equality set of the versions is measurable (StronglyMeasurable.measurableSet_eq_fun). So σ_r is a.e.-strongly measurable for H.restrict M_r.

5. (θ_r is measurable on M_r.)
   - U is σ-compact: an open subset of ℝ^P is a locally compact second-countable space, so IsSigmaCompact U. Explicitly, U = ⋃_j K_j with K_j := {x ∈ U : |x| ≤ j, dist(x, ℝ^P ∖ U) ≥ 1/j}, or K_j := closedBall 0 j if U = ℝ^P.
   - So M_r = ⋃_j (M_r ∩ K_j), and θ_r is integrable, hence a.e.-strongly measurable, on each M_r ∩ K_j.
   - By aestronglyMeasurable_iUnion_iff, θ_r is a.e.-strongly measurable for H.restrict M_r.

6. (Integer multiplicity θ̂.) Let t_r := 1_{M_r}·(c_r·σ_r·θ_r), so t_r = 0 if r ∉ I, and let θ̂(x) := Σ'_r t_r(x) (a real tsum).
   - Each t_r is a.e.-strongly measurable for H (steps 4–5 and aestronglyMeasurable_indicator_iff₀).
   - For x ∈ G, t_r(x) = 0 for r ∉ F(x), which is a finite set. So θ̂(x) = Σ_{r∈F(x)} c_r·σ_r(x)·θ_r(x) (tsum_eq_sum) is a finite sum of integers, and θ̂(x) ∈ ℤ.
   - Moreover |θ̂(x)| ≤ Σ_{r∈F(x)} |c_r|·θ_r(x), hence ofReal|θ̂(x)| ≤ Σ_{r∈F(x)} |c_r|·ofReal θ_r(x) ≤ Θ(x) (ENNReal.sum_le_tsum).
   - For x ∈ G, the partial sums Σ_{r<N} t_r(x) equal θ̂(x) once N > max F(x). So they converge to θ̂ H-a.e., and θ̂ is a.e.-strongly measurable for H (aestronglyMeasurable_of_tendsto_ae).

7. (The new triple.) Define
   M' := {x ∈ M_∪ ∩ G : θ̂(x) ≠ 0},   θ' := 1_{M'}·|θ̂|,   ξ' := 1_{M'}·((θ̂/|θ̂|) • ξ̂).
   For x ∈ M':
   - θ̂(x)/|θ̂(x)| ∈ {1, −1};
   - θ'(x) = |θ̂(x)| = (θ̂(x)).natAbs ∈ ℕ by step 6, and θ'(x) > 0;
   - θ'(x)·ξ'(x) = θ̂(x)·ξ̂(x).

8. (Pointwise identity.) Fix ω ∈ D^n(U) and let F_r(x) := 1_{M_r}(x)·(c_r·(θ_r(x)·ξ_r(x)(ω(x)))), the integrand of the sibling tsum_tau. Let x ∈ G.
   - If x ∉ M_∪: every F_r(x) = 0 (either c_r = 0 or x ∉ M_r), and x ∉ M'. So Σ'_r F_r(x) = 0 = 1_{M'}(x)·θ'(x)·ξ'(x)(ω(x)).
   - If x ∈ M_∪: F_r(x) = 0 for r ∉ F(x), and F_r(x) = c_r·θ_r(x)·σ_r(x)·ξ̂(x)(ω(x)) for r ∈ F(x) by step 4. Hence Σ'_r F_r(x) = θ̂(x)·ξ̂(x)(ω(x)) (tsum of a finitely supported family, step 6).
     • If θ̂(x) ≠ 0, then x ∈ M' and this equals θ'(x)·ξ'(x)(ω(x)) (step 7).
     • If θ̂(x) = 0, then x ∉ M' and both sides are 0.
   So Σ'_r F_r = 1_{M'}·θ'·ξ'(ω) on G, i.e. H-a.e.

9. (HasSum.)
   - The sibling tsum_tau (same hypotheses) gives HasSum (r ↦ c_r·tauAction n M_r θ_r ξ_r ω) (∫ Σ'_r F_r dH).
   - By step 8 (integral_congr_ae) and integral_indicator₀ (M' is null-measurable, step 10(ii)):
     ∫ Σ'_r F_r dH = ∫_{M'} θ'(x)·ξ'(x)(ω(x)) dH = tauAction n M' θ' ξ' ω.

10. (Triple conditions for (M', θ', ξ').)
   (i) subset: M' ⊆ M_∪ ⊆ U.
   (ii) nullMeasurableSet: M' = M_∪ ∩ G ∩ {θ̂ ≠ 0}. M_∪ is null-measurable, G is measurable, and {θ̂ ≠ 0} is null-measurable because θ̂ is a.e.-measurable (step 6).
   (iii) countablyRectifiable: M' ⊆ M_∪ = ⋃_r M̃_r with M̃_r := M_r for r ∈ I and M̃_r := ∅ otherwise.
       - Each M̃_r is countably n-rectifiable: field countablyRectifiable, and ∅ via countablyRectifiable_of_measure_zero.
       - Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion and CountablyRectifiable.mono give CountablyRectifiable n M'.
   (iv) pos, and θ' natural-valued on M': step 7.
   (v) integrableOn: let K ⊆ U be compact.
       - θ' is a.e.-strongly measurable (step 6, indicator of the null-measurable M') and θ' ≥ 0.
       - For x ∈ M' (⊆ G), ofReal θ'(x) = ofReal|θ̂(x)| ≤ Θ(x) (step 6).
       - So ∫⁻_{M'∩K} ofReal θ' dH ≤ ∫⁻_K Θ dH < ∞ (step 1(a)), and θ' is integrable on M' ∩ K.
   (vi) aestronglyMeasurable: θ̂/|θ̂| is a.e.-measurable (a quotient of a.e.-measurable real functions), and ξ̂ is a.e.-strongly measurable for H.restrict M_∪, hence for H.restrict M'. So (θ̂/|θ̂|) • ξ̂ is a.e.-strongly measurable for H.restrict M', and so is ξ', which agrees with it on M'.
   (vii) orients:
       - For each r ∈ I apply hTL to (M_r, θ_r) and (M', θ'). Its hypotheses are the fields of the r-th triple together with (i), (ii), (iv), (v).
       - Via ae_restrict_iff'₀ (M_r ∩ M' null-measurable) this gives null sets N'_r such that, for x ∈ (M_r ∩ M') ∖ N'_r, every weighted approximate tangent space of (M_r, θ_r) at x is one of (M', θ') at x.
       - Let x ∈ M' ∖ ⋃_{r∈I} N'_r and r := r(x) ∈ I. Then x ∈ M_r and x ∈ G, so x ∉ N_r.
       - By 1(b) there is an orthonormal τ with HasWeightedApproximateTangentSpaceAt n M_r θ_r x (span(range τ)) and ξ_r(x) = ±s(τ).
       - As x ∈ (M_r ∩ M') ∖ N'_r, also HasWeightedApproximateTangentSpaceAt n M' θ' x (span(range τ)).
       - Finally ξ'(x) = (θ̂(x)/|θ̂(x)|)·ξ̂(x) = ±ξ_r(x) = ±s(τ).
       - Since ⋃_{r∈I} N'_r is null, this holds for H.restrict M'-a.e. x (ae_restrict_iff'₀).
   Hence IsRectifiableTriple U n M' θ' ξ' holds. Together with step 7 (θ' natural-valued on M') and step 9, this proves the theorem. ∎

## Key steps

1. null sets: overlap_finite (finite overlaps, ∫_K Θ < ∞), the orientation conditions, and orientation_sign for all pairs (locality from hTL)
2. first-index reference orientation ξ̂ glued from ξ_r on A_r; signs σ_r with ξ_r = σ_r ξ̂ on M_r off the null set
3. θ̂ := Σ' 1_{M_r} c_r σ_r θ_r is an a.e.-measurable, integer-valued finite sum with |θ̂| ≤ Θ
4. M' := (M_∪ ∖ N₀) ∩ {θ̂ ≠ 0}, θ' := |θ̂|, ξ' := (θ̂/|θ̂|)ξ̂; Σ'F_r = 1_{M'} θ' ξ'(ω) a.e.
5. tsum_tau gives HasSum with limit tauAction(M', θ', ξ')(ω)
6. triple conditions; orientation of M' via hTL applied to (M_r, θ_r) and (M', θ')

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (identical); read IsRectifiableTriple, tauAction, IsIntegerMultiplicity, CompactlyContainedOpen; sed GMT/Ch06/README.md (reused SimonGMT definitions, NVector ContinuousENorm remark)`
- `grep '^theorem|^def|^structure|^abbrev' SimonGMT Chapter06/{Currents,Mass,Forms,FormsDuality}.lean and Chapter03/Rectifiable.lean (massAdmissibleOn, massOn, le_massOn, covectorEuclideanNorm, TestFormOnConverges, simpleNVector via mkContinuous, wedgeCovectors_apply_det, CountablyRectifiable.mono, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, HasWeightedApproximateTangentSpaceAt.unique)`
- `grep -rn 'simpleNVector' SimonGMT (only FormsDuality.lean); grep -rn 'tauAction|IsIntegerMultiplicity|natAbs' SimonGMT (no match); grep 'fiw_ims|simpleNVector|Orthonormal' project/GMT outside the Ch06 contract (no related lemma)`
- `rg Mathlib snapshot: exists_open_between_and_isCompact_closure, measure_null_of_locally_null, integral_tsum, hasSum_integral_of_summable_integral_norm, lintegral_tsum, integral_indicator₀, lintegral_indicator₀, ae_restrict_iff'₀, ae_restrict_mem₀, ae_lt_top', AEMeasurable.ennreal_tsum, aestronglyMeasurable_iUnion_iff, aestronglyMeasurable_indicator_iff₀, aestronglyMeasurable_of_tendsto_ae, StronglyMeasurable.measurableSet_eq_fun, ContinuousLinearMap.aestronglyMeasurable_comp₂, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, LinearMap.mkContinuous_norm_le, ContinuousAlternatingMap.le_opNorm, norm_iteratedFDeriv_zero, ENNReal.ofReal_tsum_of_nonneg, norm_tsum_le_tsum_norm, IsSigmaCompact API, PseudoMetrizableSpace definition`
- `python3 listing of dag.json lean_names and of all nodes/*/decomposition-v*.json subproblem lean_names (no fiw_ims_* reserved)`
- `git archive d8d46c9 into /tmp/ims_check.FWdVje with .lake/packages -> shared lake-packages-25730c7c; lake build GMT.Ch06.Submission (success)`
- `gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement on the 7 child statements; lake env lean Scratch/AllChildren.lean (0 errors)`
- `lake env lean Scratch/Assembly.lean: #print axioms Submission.fiw_im_series = [propext, sorryAx, Classical.choice, Quot.sound] (sorryAx only from stubbed children/prerequisites)`
- `lake env lean Scratch/Plumbing.lean (im_combine hypotheses feed overlap_finite, tsum_tau, orientation_sign; 0 errors)`
- `lake env lean Scratch/Inst{2,3,6,8,9}.lean: #synth on NVector (Eucl P) n; local PseudoMetrizableSpace via UniformSpace.pseudoMetrizableSpace + EMetric.instIsCountablyGeneratedUniformity; isBoundedBilinearMap_apply.continuous measurability route; |simpleNVector τ α| ≤ ‖α‖ for orthonormal τ`
- `book/chapter-06.txt: 3.2 Remarks (1),(3), 3.13 Lemma and proof, use of 3.13 for R^(ℓ), S^(ℓ) in the proof of 7.2`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Metrizable/Uniformity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ims_check.FWdVje/Scratch/AllChildren.lean`
- `/tmp/ims_check.FWdVje/Scratch/Assembly.lean`
- `/tmp/ims_check.FWdVje/Scratch/Plumbing.lean`
- `/tmp/ims_check.FWdVje/Scratch/Inst6.lean`
- `/tmp/ims_check.FWdVje/Scratch/Inst8.lean`
- `/tmp/ims_check.FWdVje/Scratch/Inst9.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract (Contract.lean = Submission.lean). The pinned SimonGMT has the needed library pieces:
- massAdmissibleOn, massOn, le_massOn and covectorEuclideanNorm;
- TestFormOnConverges;
- simpleNVector, defined by mkContinuous with bound ∏‖v_i‖;
- CountablyRectifiable.mono, countablyRectifiable_iUnion and HasWeightedApproximateTangentSpaceAt.unique.
It has no integer-multiplicity calculus, mass bound, frame-sign or termwise-integration lemma (simpleNVector is used nowhere else; tauAction and IsIntegerMultiplicity appear only in the contract), so these become the children.

Mathlib supplies every tool cited in the child proofs: exists_open_between_and_isCompact_closure, measure_null_of_locally_null, lintegral_tsum, integral_tsum and hasSum_integral_of_summable_integral_norm, the indicator₀ and ae_restrict₀ lemmas, aestronglyMeasurable_iUnion_iff and aestronglyMeasurable_of_tendsto_ae, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, and ContinuousAlternatingMap.le_opNorm.

At this pin, NVector (Eucl P) n lacks PseudoMetrizableSpace, MetrizableSpace, ContinuousAdd and SecondCountableTopology instances via search. A local PseudoMetrizableSpace instance and the isBoundedBilinearMap_apply.continuous route compile, and are recorded in the proofs.

Scratch build of the frozen commit:
- all 7 child types elaborate in the comparator's exact child scope;
- fiw_im_series is derived from fiw_ims_series_current, fiw_ims_combine and the two prerequisite stubs (axioms propext, Classical.choice, Quot.sound plus sorryAx from stubs only);
- the child-to-child plumbing type-checks.

No fiw_ims_* name is reserved in the DAG. Book 3.13 proves completeness via L¹ convergence of multiplicities. The supplied series proof (steps 1–9) is the contract followed here.
