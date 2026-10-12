# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.mass_representation-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1.riesz_borel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with standard basis b_i = EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin P) ℝ i (i ∈ Fin P). A k-covector is α ∈ Covector (Eucl P) k (a continuous alternating k-linear map ℝ^P → ℝ) with operator norm ‖α‖; |α| := covectorEuclideanNorm α = (Σ_{I : Fin k → Fin P strictly increasing} α(b_{I(0)},…,b_{I(k−1)})²)^{1/2}. A k-vector is w ∈ NVector (Eucl P) k, a continuous linear functional on k-covectors. D^k(U) = TestFormOn U k (smooth, compactly supported forms with tsupport ⊆ U), D_k(U) = GeometricCurrentOn U k, M_W(T) = T.massOn W = sup{ENNReal.ofReal(T(ω)) : ω ∈ D^k(U), tsupport ω ⊆ W, |ω(x)| ≤ 1 ∀x} (massAdmissibleOn). CF(U) := {φ : ℝ^P → Covector (Eucl P) k : φ continuous, HasCompactSupport φ, tsupport φ ⊆ U}. All measures are Borel measures on ℝ^P; ∫_A f dμ means ∫ x in A, f x ∂μ (integral for μ.restrict A). Source: Simon, Introduction to GMT, Ch. 6, 2.7–2.9 (pp. 136–137), with Ch. 1, 4.14 (Riesz) and 1.17 (Lusin); this argument is extracted from the parent proof of slicing_mass_representation (its steps are cited as P1–P7).

This is step P3 and the measure-theoretic part of step P4 of the parent proof. Notation: H := EuclideanSpace ℝ (Fin N), a finite-dimensional real inner product space (second countable, Borel σ-algebra); Y := U with the subspace topology (the subtype ↥U); ι : Y → ℝ^P the inclusion.

1. (The space Y.) Y is Hausdorff and second countable, and locally compact because U is an open subset of the locally compact space ℝ^P (IsOpen.locallyCompactSpace); hence Y is σ-compact. The Borel σ-algebra of Y is the subspace σ-algebra (Subtype.borelSpace), and ι is a measurable embedding with Borel range U (MeasurableEmbedding.subtype_coe, U open).
2. (Extension by zero.) For g ∈ C_c(Y, H) let ĝ : ℝ^P → H be ĝ(x) := g(x) for x ∈ U and ĝ(x) := 0 for x ∉ U. C := ι(tsupport g) is a compact subset of U, closed in ℝ^P. ĝ is continuous: on the open set U it agrees with g (transported along ι); a point x ∉ U has the open neighbourhood ℝ^P ∖ C on which ĝ = 0. Moreover support ĝ ⊆ C, so tsupport ĝ ⊆ C ⊆ U and ĝ has compact support: ĝ ∈ CF_N(U). Clearly (g + h)^ = ĝ + ĥ, (cg)^ = c·ĝ and ‖ĝ(x)‖ ≤ sup_y ‖g(y)‖. Conversely, if f ∈ CF_N(U), then g := f ∘ ι is continuous on Y and its support lies in ι⁻¹(tsupport f), which is compact in Y (tsupport f is a compact subset of U and ι is an embedding), so g ∈ C_c(Y, H); and ĝ = f because f vanishes off tsupport f ⊆ U.
3. (The functional on Y.) Define L′ : C_c(Y, H) → ℝ by L′(g) := L(ĝ). By step 2 and the additivity and homogeneity of L on CF_N(U), L′ is ℝ-linear. L′ satisfies IsLocallyBoundedCcFunctional: for compact K_Y ⊆ Y, K := ι(K_Y) is a compact subset of U with bound B_K; if g ∈ C_c(Y, H), ‖g(y)‖ ≤ 1 for all y and tsupport g ⊆ K_Y, then ĝ is continuous, tsupport ĝ ⊆ ι(tsupport g) ⊆ K and ‖ĝ(x)‖ ≤ 1, so L′(g) = L(ĝ) ≤ B_K. Hence L′ '' {g : (∀ y, ‖g(y)‖ ≤ 1) ∧ tsupport g ⊆ K_Y} is bounded above.
4. (Riesz.) By Poincare.SimonGMT.Chapter01.simon_theorem_4_14 (Simon Ch. 1, Theorem 4.14) for the locally compact Hausdorff space Y and the finite-dimensional real inner product space H, there are an outer measure μ₀ on Y with hμ₀ : IsRadonOuterMeasure μ₀ (Borel regular, finite on compact sets, outer and inner regular) and ν₀ : Y → H, measurable for the Carathéodory σ-algebra of μ₀, with ‖ν₀(y)‖ = 1 for μ_C-a.e. y and L′(g) = ∫_Y ⟨g(y), ν₀(y)⟩ dμ_C(y) for all g ∈ C_c(Y, H), where μ_C := hμ₀.toCaratheodoryMeasure.
5. (Borel measure on Y.) Let m := hμ₀.borel_regular.toBorelMeasure, a measure on the Borel σ-algebra of Y with m(A) = μ₀(A) for every A ⊆ Y (IsBorelRegularOuterMeasure.toBorelMeasure_apply_all); also μ_C(A) = μ₀(A) for every A (IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all). Hence m and μ_C have the same null sets, the Borel σ-algebra is contained in the Carathéodory σ-algebra, and m is the trim of μ_C to the Borel σ-algebra (they agree on Borel sets). Also m(K) = μ₀(K) < ∞ for every compact K ⊆ Y.
6. (Borel modification of ν₀.) Y is σ-compact and μ₀ is finite on compact sets, so μ₀ is open-σ-finite (isOpenSigmaFinite_of_finite_compacts). Therefore every Carathéodory-measurable A ⊆ Y contains a Borel set B with μ₀(A ∖ B) = 0 (IsBorelRegularOuterMeasure.exists_borel_subset_mod_null), and by Borel regularity A ∖ B is contained in a Borel μ₀-null set; thus A is m-null-measurable. Consequently ν₀ is m-null-measurable (preimages of Borel sets of H are Carathéodory-measurable), hence a.e.-measurable for m because H is second countable (MeasureTheory.NullMeasurable.aemeasurable): there is a Borel map ν₀′ : Y → H with ν₀′ = ν₀ m-a.e., equivalently μ_C-a.e. (same null sets). Put ν₁(y) := ν₀′(y) if ‖ν₀′(y)‖ = 1 and ν₁(y) := 0 otherwise. Then ν₁ is Borel, ‖ν₁(y)‖ ≤ 1 for every y, and, since ‖ν₀‖ = 1 μ_C-a.e., ν₁ = ν₀ and ‖ν₁‖ = 1 hold m-a.e. and μ_C-a.e.
7. (Representation on Y with Borel data.) For g ∈ C_c(Y, H), y ↦ ⟨g(y), ν₁(y)⟩ is Borel and equals ⟨g(y), ν₀(y)⟩ for μ_C-a.e. y. Hence L′(g) = ∫⟨g, ν₀⟩ dμ_C = ∫⟨g, ν₁⟩ dμ_C = ∫⟨g, ν₁⟩ dm, the last equality by integral_trim (the integrand is strongly measurable for the Borel σ-algebra and m is the trim of μ_C).
8. (Push-forward to ℝ^P.) Let μ := m.map ι, a Borel measure on ℝ^P with μ(A) = m(ι⁻¹A) for Borel A, and let ν(x) := ν₁(⟨x, hx⟩) for x ∈ U, ν(x) := 0 for x ∉ U. ν is Borel (it is piecewise on the Borel set U, and ν ∘ ι = ν₁ is Borel) and ‖ν(x)‖ ≤ 1 for all x. μ(ℝ^P ∖ U) = m(ι⁻¹(ℝ^P ∖ U)) = m(∅) = 0. If K ⊆ U is compact, then ι⁻¹(K) is compact in Y, so μ(K) = m(ι⁻¹K) < ∞. Finally μ{x : ‖ν(x)‖ ≠ 1} = m{y : ‖ν₁(y)‖ ≠ 1} = 0, so ‖ν‖ = 1 μ-a.e.
9. (Representation and integrability.) Let f ∈ CF_N(U) and g := f ∘ ι ∈ C_c(Y, H), so ĝ = f (step 2). The function x ↦ ⟨f(x), ν(x)⟩ is Borel, bounded by sup‖f‖ (as ‖ν‖ ≤ 1), and vanishes off the compact set tsupport f ⊆ U, which has finite μ-measure; hence it is μ-integrable. By MeasurableEmbedding.integral_map, ∫⟨f(x), ν(x)⟩ dμ(x) = ∫_Y ⟨f(ι y), ν(ι y)⟩ dm(y) = ∫_Y ⟨g(y), ν₁(y)⟩ dm(y) = L′(g) (step 7) = L(ĝ) = L(f). ∎

Formalization note (not part of the argument): simon_theorem_4_14, IsRadonOuterMeasure, isOpenSigmaFinite_of_finite_compacts and exists_borel_subset_mod_null are not imported by GMT.Ch06.Submission; add `import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation` and `import Poincare.SimonGMT.Chapter01.RegularityCompletion` (checked to compile with the frozen submission). The local instances LocallyCompactSpace ↥U (IsOpen.locallyCompactSpace) and SigmaCompactSpace ↥U may need to be provided explicitly.

## Key steps

1. Y := U is a locally compact, σ-compact Hausdorff space; zero extension g ↦ ĝ identifies C_c(Y, ℝ^N) with CF_N(U).
2. L′(g) := L(ĝ) is linear and IsLocallyBoundedCcFunctional; apply simon_theorem_4_14 on Y.
3. Replace the Carathéodory measure by its Borel restriction m and ν₀ by a Borel ν₁ with ‖ν₁‖ ≤ 1 everywhere and = 1 a.e. (Borel regularity, open σ-finiteness, NullMeasurable.aemeasurable, integral_trim).
4. Push forward μ := m.map ι and extend ν₁ by 0 to ν; μ(Uᶜ) = 0, μ finite on compact subsets of U.
5. Representation L(f) = ∫⟨f, ν⟩ dμ and integrability via MeasurableEmbedding.integral_map.

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
