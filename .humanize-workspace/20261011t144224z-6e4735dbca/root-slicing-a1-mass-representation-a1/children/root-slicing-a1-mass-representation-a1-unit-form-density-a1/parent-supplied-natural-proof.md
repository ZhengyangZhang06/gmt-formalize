# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.mass_representation-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1.unit_form_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with standard basis b_i = EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin P) ℝ i (i ∈ Fin P). A k-covector is α ∈ Covector (Eucl P) k (a continuous alternating k-linear map ℝ^P → ℝ) with operator norm ‖α‖; |α| := covectorEuclideanNorm α = (Σ_{I : Fin k → Fin P strictly increasing} α(b_{I(0)},…,b_{I(k−1)})²)^{1/2}. A k-vector is w ∈ NVector (Eucl P) k, a continuous linear functional on k-covectors. D^k(U) = TestFormOn U k (smooth, compactly supported forms with tsupport ⊆ U), D_k(U) = GeometricCurrentOn U k, M_W(T) = T.massOn W = sup{ENNReal.ofReal(T(ω)) : ω ∈ D^k(U), tsupport ω ⊆ W, |ω(x)| ≤ 1 ∀x} (massAdmissibleOn). CF(U) := {φ : ℝ^P → Covector (Eucl P) k : φ continuous, HasCompactSupport φ, tsupport φ ⊆ U}. All measures are Borel measures on ℝ^P; ∫_A f dμ means ∫ x in A, f x ∂μ (integral for μ.restrict A). Source: Simon, Introduction to GMT, Ch. 6, 2.7–2.9 (pp. 136–137), with Ch. 1, 4.14 (Riesz) and 1.17 (Lusin); this argument is extracted from the parent proof of slicing_mass_representation (its steps are cited as P1–P7).

This is step P6(≥)(i)–(iv) of the parent proof, with the unit field written in the coordinates of the isometry J.

1. (Coordinates of v.) By the sibling theorem smr_covector_coord_isometry choose N and a linear equivalence J : Covector (Eucl P) k ≃ₗ[ℝ] H := EuclideanSpace ℝ (Fin N) with |α| = ‖Jα‖; J⁻¹ is continuous (finite dimension) and |J⁻¹h| = ‖h‖. Let h_1, …, h_N be the standard basis of H and define u : ℝ^P → H by u(x)_i := v(x)(J⁻¹h_i). Each coordinate is Borel by hypothesis, so u is Borel. For every α, Jα = Σ_i (Jα)_i h_i, so α = Σ_i (Jα)_i J⁻¹h_i and, v(x) being linear, v(x)(α) = Σ_i (Jα)_i u(x)_i = ⟨Jα, u(x)⟩.
2. (‖u‖ ≤ 1 everywhere, = 1 a.e.) For every x, with α := J⁻¹u(x): ‖u(x)‖² = ⟨u(x), u(x)⟩ = v(x)(α) ≤ |α| = ‖u(x)‖, hence ‖u(x)‖ ≤ 1. If |α| ≤ 1 and v(x)(α) = 1 for some α, then 1 = ⟨Jα, u(x)⟩ ≤ ‖Jα‖·‖u(x)‖ ≤ ‖u(x)‖. Hence G := {x : ‖u(x)‖ = 1} is a Borel set with μ(ℝ^P ∖ G) = 0.
3. (Compact inner approximation.) Since c < μ(W ∩ A), c < ∞. The open set W ⊆ ℝ^P is σ-compact: W = ⋃_j K_j with compact K_j ⊆ K_{j+1} (e.g. a compact exhaustion of the locally compact second countable subspace W; concretely K_j := {x : ‖x‖ ≤ j, dist(x, ℝ^P ∖ W) ≥ 1/(j+1)} if W ≠ ℝ^P and K_j := closed ball of radius j if W = ℝ^P). By continuity from below, μ(W ∩ A ∩ G ∩ K_j) ↑ μ(W ∩ A ∩ G) = μ(W ∩ A) > c (G is conull), so there is j with c < μ(E) for the Borel set E := W ∩ A ∩ G ∩ K_j, and μ(E) ≤ μ(K_j) < ∞ (K_j is a compact subset of W ⊆ U). Every Borel measure on the Polish space ℝ^P is inner regular by compact sets on Borel sets of finite measure (instance InnerRegularCompactLTTop; MeasurableSet.exists_lt_isCompact_of_ne_top), so there is a compact C ⊆ E with c < μ(C) < ∞; thus C ⊆ W ∩ A ∩ G. Let d := (μ(C).toReal − c.toReal)/3 > 0.
4. (Lusin.) The measure μ is inner regular by closed (indeed compact) sets on Borel sets of finite measure (step 3), which is the regularity hypothesis of Lusin's theorem Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable (Simon Ch. 1, 1.17). If N = 0 then H = {0}, G = ∅ and C = ∅, contradicting μ(C) > c ≥ 0; so N ≥ 1. Applying Lusin's theorem to the Borel set C (μ(C) < ∞) and each Borel coordinate u_i, i = 1, …, N, gives closed F_i ⊆ C with μ(C ∖ F_i) < d/N and u_i continuous on F_i. Let C′ := ⋂_i F_i, a closed subset of the compact set C, hence compact; μ(C ∖ C′) ≤ Σ_i μ(C ∖ F_i) < d, and u is continuous on C′ (all coordinates are). Thus μ(C′) > μ(C) − d and C′ ⊆ C ⊆ W ∩ A ∩ G.
5. (Tietze.) u restricted to C′ is a continuous map into the closed unit ball B̄ of H (step 2). The closed unit ball of a finite-dimensional real normed space has the Tietze extension property (Set.instTietzeExtensionUnitClosedBall; alternatively extend each coordinate by Tietze's theorem and compose with the continuous retraction y ↦ y/max(1, ‖y‖)), and C′ is closed, so there is a continuous ũ : ℝ^P → H with ‖ũ(x)‖ ≤ 1 for all x and ũ = u on C′ (ContinuousMap.exists_restrict_eq).
6. (Small open neighbourhood.) Since C′ is compact and W open, choose r > 0 with K″ := cthickening r C′ ⊆ W (IsCompact.exists_cthickening_subset_open). K″ is closed and bounded, hence compact, and K″ ⊆ U, so μ(K″) < ∞. The open sets O_j := thickening (r/(j+1)) C′ decrease, ⋂_j O_j = closure C′ = C′ (closure_eq_iInter_thickening), and μ(O_0) ≤ μ(K″) < ∞. By continuity from above applied to the decreasing Borel sets O_j ∖ C′ (with empty intersection), μ(O_j ∖ C′) → 0, so there is j with μ(O_j ∖ C′) < d. Let O := O_j; then O is open, C′ ⊆ O, μ(O ∖ C′) < d and closure O ⊆ cthickening (r/(j+1)) C′ ⊆ K″ ⊆ W.
7. (Urysohn.) By exists_continuous_one_zero_of_isCompact (C′ compact, ℝ^P ∖ O closed and disjoint from C′) there is a continuous ψ : ℝ^P → ℝ with values in [0, 1], ψ = 1 on C′, ψ = 0 on ℝ^P ∖ O, and compact support. Then support ψ ⊆ O and tsupport ψ ⊆ closure O ⊆ W.
8. (The form.) Define φ(x) := ψ(x)·J⁻¹(ũ(x)). φ is continuous; support φ ⊆ support ψ, so φ has compact support and tsupport φ ⊆ tsupport ψ ⊆ W; and |φ(x)| = ψ(x)·‖ũ(x)‖ ≤ 1. By step 1, g(x) := v(x)(φ(x)) = ψ(x)·⟨ũ(x), u(x)⟩. Hence g is Borel (ψ and ũ continuous, u Borel); |g(x)| ≤ |φ(x)| ≤ 1 (hypothesis on v); g = 0 off O; and for x ∈ C′, g(x) = ⟨u(x), u(x)⟩ = ‖u(x)‖² = 1 because C′ ⊆ G. Being bounded, Borel and zero off O ⊆ K″ with μ(K″) < ∞, g is μ-integrable and μ⌞A-integrable.
9. (Estimate.) Since C′ ⊆ A and C′ is Borel, ∫_A g dμ = ∫_{C′} g dμ + ∫_{A ∖ C′} g dμ = μ(C′).toReal + ∫_{A ∖ C′} g dμ, and |∫_{A ∖ C′} g dμ| ≤ ∫_{A ∖ C′} |g| dμ ≤ μ((A ∖ C′) ∩ O).toReal ≤ μ(O ∖ C′).toReal < d (g = 0 off O and |g| ≤ 1). Therefore ∫_A g dμ > (μ(C).toReal − d) − d = c.toReal + d > c.toReal, and as c < ∞ this gives c < ENNReal.ofReal(∫_A v(x)(φ(x)) dμ(x)). With step 8, φ has all required properties. ∎

Formalization note (not part of the argument): Lusin's theorem and the Tietze instances are not imported by GMT.Ch06.Submission; add `import Poincare.SimonGMT.Chapter01.Lusin`, `import Mathlib.Topology.TietzeExtension` and `import Mathlib.Analysis.Complex.Tietze` (the last provides TietzeExtension (Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)); checked to compile with the frozen submission.

## Key steps

1. Coordinates u(x) := (v(x)(J⁻¹h_i))_i via the isometry J, so v(x)(α) = ⟨Jα, u(x)⟩, u Borel, ‖u‖ ≤ 1 everywhere and ‖u‖ = 1 μ-a.e.
2. Compact C ⊆ W ∩ A ∩ {‖u‖ = 1} with c < μ(C) < ∞ (σ-compactness of W, continuity from below, inner regularity).
3. Lusin (SimonGMT exists_isClosed_continuousOn_of_measurable) on each coordinate: compact C′ ⊆ C, μ(C ∖ C′) < d, u continuous on C′.
4. Tietze: continuous ũ : ℝ^P → closed unit ball of ℝ^N extending u|C′.
5. Open O ⊇ C′ with μ(O ∖ C′) < d and closure O ⊆ W; Urysohn cutoff ψ.
6. φ := ψ·J⁻¹ũ has |φ| ≤ 1, tsupport ⊆ W and ∫_A v(φ) dμ ≥ μ(C′) − μ(O ∖ C′) > c.

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
