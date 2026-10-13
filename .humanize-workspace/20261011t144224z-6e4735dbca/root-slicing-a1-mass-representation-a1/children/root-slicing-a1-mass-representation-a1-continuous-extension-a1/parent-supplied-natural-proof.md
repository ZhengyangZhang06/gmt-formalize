# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.mass_representation-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1.continuous_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with standard basis b_i = EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin P) ℝ i (i ∈ Fin P). A k-covector is α ∈ Covector (Eucl P) k (a continuous alternating k-linear map ℝ^P → ℝ) with operator norm ‖α‖; |α| := covectorEuclideanNorm α = (Σ_{I : Fin k → Fin P strictly increasing} α(b_{I(0)},…,b_{I(k−1)})²)^{1/2}. A k-vector is w ∈ NVector (Eucl P) k, a continuous linear functional on k-covectors. D^k(U) = TestFormOn U k (smooth, compactly supported forms with tsupport ⊆ U), D_k(U) = GeometricCurrentOn U k, M_W(T) = T.massOn W = sup{ENNReal.ofReal(T(ω)) : ω ∈ D^k(U), tsupport ω ⊆ W, |ω(x)| ≤ 1 ∀x} (massAdmissibleOn). CF(U) := {φ : ℝ^P → Covector (Eucl P) k : φ continuous, HasCompactSupport φ, tsupport φ ⊆ U}. All measures are Borel measures on ℝ^P; ∫_A f dμ means ∫ x in A, f x ∂μ (integral for μ.restrict A). Source: Simon, Introduction to GMT, Ch. 6, 2.7–2.9 (pp. 136–137), with Ch. 1, 4.14 (Riesz) and 1.17 (Lusin); this argument is extracted from the parent proof of slicing_mass_representation (its steps are cited as P1–P7).

This is steps P1–P2 of the parent proof. Write V ⊂⊂ U for CompactlyContainedOpen V U (V open, closure V compact, closure V ⊆ U); for such V the hypothesis gives X.massOn V < ∞, and we put M_V := (X.massOn V).toReal ∈ [0, ∞).

0. (Seminorm properties.) By the sibling theorem smr_covector_coord_isometry there are N and a linear J with |α| = ‖J α‖ for all α. Hence |α + β| ≤ |α| + |β|, |cα| = |c|·|α| and |α| ≥ 0 for all covectors α, β and c ∈ ℝ.
1. (Neighbourhoods.) If K ⊆ U is compact, there is V ⊂⊂ U with K ⊆ V (exists_open_between_and_isCompact_closure: ℝ^P is locally compact and regular, U is open). If V₁, V₂ ⊂⊂ U then V₁ ∪ V₂ ⊂⊂ U, since closure(V₁ ∪ V₂) = closure V₁ ∪ closure V₂ is compact and contained in U. Every φ ∈ CF(U) has compact tsupport φ ⊆ U; fix (by choice) V_φ ⊂⊂ U with tsupport φ ⊆ V_φ.
2. (Mass estimate, P1.) Let V ⊂⊂ U, ω ∈ D^k(U) with tsupport ω ⊆ V and |ω(x)| ≤ C for all x. Then |X(ω)| ≤ M_V·C. Proof: C ≥ |ω(0)| ≥ 0. Let s > C, so s > 0. The forms s⁻¹ω and −s⁻¹ω lie in D^k(U), have tsupport ⊆ tsupport ω ⊆ V and satisfy |±s⁻¹ω(x)| = s⁻¹|ω(x)| ≤ 1, so they belong to massAdmissibleOn U k V. By GeometricCurrentOn.le_massOn and linearity of X, ENNReal.ofReal(±s⁻¹X(ω)) ≤ X.massOn V < ∞, hence ±s⁻¹X(ω) ≤ M_V, i.e. |X(ω)| ≤ s·M_V. Letting s ↓ C gives |X(ω)| ≤ M_V·C.
3. (Approximants.) For φ ∈ CF(U) and j ∈ ℕ apply the sibling theorem smr_exists_testForm_uniform_approx with the open set V := V_φ (V_φ ⊆ closure V_φ ⊆ U) and ε := 1/(j+1) to choose η_j(φ) ∈ D^k(U) with tsupport η_j(φ) ⊆ V_φ and |φ(x) − η_j(φ)(x)| ≤ 1/(j+1) for all x.
4. (Definition of L.) For φ ∈ CF(U), (X(η_j(φ)))_j is Cauchy: η_i(φ) − η_j(φ) ∈ D^k(U) has tsupport ⊆ V_φ and |η_i(φ)(x) − η_j(φ)(x)| ≤ 1/(i+1) + 1/(j+1) (step 0), so by step 2 and linearity |X(η_i(φ)) − X(η_j(φ))| ≤ M_{V_φ}·(1/(i+1) + 1/(j+1)). Define L(φ) := lim_j X(η_j(φ)) for φ ∈ CF(U), and L(φ) := 0 for φ ∉ CF(U).
5. (Independence of the approximating sequence.) Claim: if φ ∈ CF(U), V ⊂⊂ U, ζ_j ∈ D^k(U) with tsupport ζ_j ⊆ V for all j, and real numbers d_j → 0 with |ζ_j(x) − φ(x)| ≤ d_j for all x and j, then X(ζ_j) → L(φ). Proof: V′ := V ∪ V_φ ⊂⊂ U (step 1); ζ_j − η_j(φ) ∈ D^k(U) has tsupport ⊆ V′ and |ζ_j(x) − η_j(φ)(x)| ≤ d_j + 1/(j+1) (step 0). By step 2, |X(ζ_j) − X(η_j(φ))| ≤ M_{V′}·(d_j + 1/(j+1)) → 0, and X(η_j(φ)) → L(φ) by step 4.
6. (Property (1).) Let ω ∈ D^k(U). ω is continuous (it is C^∞), has compact support and tsupport ω ⊆ U, so ω ∈ CF(U). The constant sequence ζ_j := ω with V := V_ω and d_j := 0 satisfies the claim of step 5, so the constant sequence X(ω) converges to L(ω): L(ω) = X(ω).
7. (Property (2).) Let φ, ψ ∈ CF(U). φ + ψ is continuous, has compact support and tsupport(φ + ψ) ⊆ tsupport φ ∪ tsupport ψ ⊆ U, so φ + ψ ∈ CF(U). ζ_j := η_j(φ) + η_j(ψ) ∈ D^k(U) has tsupport ⊆ V_φ ∪ V_ψ ⊂⊂ U and |ζ_j(x) − (φ + ψ)(x)| ≤ 2/(j+1). By step 5, X(ζ_j) → L(φ + ψ); but X(ζ_j) = X(η_j(φ)) + X(η_j(ψ)) → L(φ) + L(ψ) (step 4). Hence L(φ + ψ) = L(φ) + L(ψ).
8. (Property (3).) Let c ∈ ℝ and φ ∈ CF(U). cφ ∈ CF(U); ζ_j := c·η_j(φ) ∈ D^k(U) has tsupport ⊆ V_φ and |ζ_j(x) − cφ(x)| ≤ |c|/(j+1). By step 5, X(ζ_j) → L(cφ), while X(ζ_j) = c·X(η_j(φ)) → c·L(φ). Hence L(cφ) = c·L(φ).
9. (Property (4).) Let K ⊆ U be compact; choose V_K ⊂⊂ U with K ⊆ V_K (step 1) and put B := 2·M_{V_K}. Let φ be continuous with tsupport φ ⊆ K and |φ(x)| ≤ 1 for all x. Then tsupport φ is a closed subset of the compact set K, so φ has compact support, and tsupport φ ⊆ U; thus φ ∈ CF(U). By smr_exists_testForm_uniform_approx (V := V_K, ε := 1/(j+1)) there are ζ_j ∈ D^k(U) with tsupport ζ_j ⊆ V_K and |φ(x) − ζ_j(x)| ≤ 1/(j+1). Then |ζ_j(x)| ≤ 1 + 1/(j+1) ≤ 2 (step 0), so |X(ζ_j)| ≤ 2·M_{V_K} = B by step 2, and X(ζ_j) → L(φ) by step 5 (d_j := 1/(j+1)). Hence |L(φ)| ≤ B. ∎

## Key steps

1. covectorEuclideanNorm is a norm (triangle inequality, homogeneity) via the isometry J of smr_covector_coord_isometry.
2. Mass estimate: |X(ω)| ≤ (X.massOn V).toReal · sup|ω| for test forms supported in V ⊂⊂ U.
3. For φ ∈ CF(U), choose V_φ ⊂⊂ U and approximants η_j(φ) ∈ D^k(U) supported in V_φ with |φ − η_j(φ)| ≤ 1/(j+1); X(η_j(φ)) is Cauchy; define L(φ) as its limit.
4. Any approximating sequence supported in a common V ⊂⊂ U gives the same limit.
5. Hence L agrees with X on test forms, is additive and homogeneous on CF(U), and |L(φ)| ≤ 2(X.massOn V_K).toReal for |φ| ≤ 1, tsupport φ ⊆ K.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean vs GMT/Ch06/Submission.lean (identical, sha256 ea3ee0dd…); read Contract.lean: Eucl, CompactlyContainedOpen, IsMeasureRepresentation, IsRestriction`
- `read simongmt Chapter06/{Mass,Currents,Forms,FormsDuality,Representation,FormSupNorm}.lean: covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn, TestFormOn, TestFormOnConverges, GeometricCurrentOn, NVector, SimonMultiIndex, wedgeCovectors_apply_det, euclideanCovectorCoordinate`
- `grep -n simon_theorem_4_14 simongmt Chapter01/RadonPolarRepresentation.lean; IsLocallyBoundedCcFunctional (VectorFunctionalEnvelope.lean); IsRadonOuterMeasure, toCaratheodoryMeasure_apply_all, isOpenSigmaFinite_of_finite_compacts (RadonOuterMeasure.lean); toBorelMeasure_apply_all (Basic.lean); exists_borel_subset_mod_null (RegularityCompletion.lean)`
- `grep -n theorem simongmt Chapter01/Lusin.lean (exists_isClosed_continuousOn_of_measurable, simon_theorem_1_17)`
- `grep -rn TietzeExtension mathlib/Mathlib (ContinuousMap.exists_restrict_eq; Set.instTietzeExtensionUnitClosedBall in Analysis/Complex/Tietze.lean)`
- `grep mathlib for UniformContinuous.exists_contDiff_dist_le, exists_open_between_and_isCompact_closure, exists_contDiff_support_eq_eq_one_iff, exists_continuous_one_zero_of_isCompact, instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace, MeasurableSet.exists_lt_isCompact_of_ne_top, IsCompact.exists_cthickening_subset_open, tendsto_measure_iInter_atTop, integral_trim, MeasurableEmbedding.integral_map, NullMeasurable.aemeasurable, aestronglyMeasurable_of_tendsto_ae, enorm_integral_le_lintegral_enorm, norm_iteratedFDeriv_zero, abs_real_inner_le_norm`
- `python3 listing of dag.json lean_name/lean_statement for all nodes; grep -rl of the nine proposed smr_ names in dag.json, nodes/ and simongmt (no matches)`
- `git show 26d9d850:GMT/Ch06/Submission.lean (kernel-checked cmb_exists_testForm_uniform_approx); git show 6c6b4b27 (cmb_covector_eq_sum_coord_smul_wedge); git show 7cdd0aed (submission adding imports)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission in scratch /tmp/smr-split-check (frozen d8d46c9, pinned shared packages)`
- `lake env lean Scratch/Challenge_*.lean (9 child types in comparator child scope, 0 errors); Scratch/Instances.lean; Scratch/Assembly.lean; Scratch/Glue5.lean; ReviewScratch/AssemblyAx.lean; ReviewScratch/UpperBound.lean (#print axioms); Scratch/Avail.lean and Scratch/Avail2.lean (which library lemmas need extra imports)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mollify-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/smr-split-check/Scratch/Assembly.lean`
- `/tmp/smr-split-check/Scratch/Glue5.lean`
- `/tmp/smr-split-check/ReviewScratch/UpperBound.lean`
- `/tmp/smr-split-check/ReviewScratch/AssemblyAx.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract and Submission, so child statements use only contract, SimonGMT and Mathlib names.

Available in SimonGMT:
- currents, massOn and covectorEuclideanNorm;
- wedgeCovectors_apply_det;
- Riesz on any locally compact Hausdorff space (simon_theorem_4_14: Radon outer measure, Carathéodory-measurable unit field);
- the Carathéodory-to-Borel tools (toBorelMeasure_apply_all, toCaratheodoryMeasure_apply_all, exists_borel_subset_mod_null, isOpenSigmaFinite_of_finite_compacts);
- Lusin's theorem (exists_isClosed_continuousOn_of_measurable).

Available in Mathlib: Tietze (including the closed unit ball of ℝ^N), Urysohn, smooth approximation and convolution, inner regularity of every Borel measure on ℝ^P, integral_trim and MeasurableEmbedding.integral_map. simon_theorem_4_14, Lusin and Tietze are not imported by GMT.Ch06.Submission; adding the corresponding imports compiles.

No existing declaration states the representation, the restriction current or the restriction mass formula. Kernel-checked templates exist in other branches for the approximation lemma (26d9d850) and the covector expansion (6c6b4b27); their names are reserved by active branches, so fresh smr_ names are used, none of which occur in the DAG, nodes/ or simongmt.

All nine child types elaborate in the comparator child scope. The parent's frozen type is kernel-checked from continuous_extension, riesz_forms, restriction_current and restriction_mass. riesz_forms is kernel-checked from covector_isometry and riesz_borel. The ≥ half of restriction_mass is kernel-checked from unit_form_density and continuous_mass_bound; its ≤ half is kernel-checked outright with axioms [propext, Classical.choice, Quot.sound]. These checks do not certify the analytic child proofs.
