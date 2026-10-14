# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 4.6–4.11 (chapter-06.txt lines 1324–1404, printed pp. 157–158): slices of a current T with M_W(T) + M_W(∂T) < ∞ by a Lipschitz function f, defined by 4.6 ⟨T, f, t₋⟩ := ∂(T⌞{f < t}) − (∂T)⌞{f < t}, the support property 4.8 and the mass inequalities 4.9–4.10. Simon proves 4.8–4.9 for f ∈ C¹ via 4.11 and says “to handle general Lipschitz f we simply use f^{(σ)} in place of f … then let σ ↓ 0”; that limiting argument is written out in step 3. Here the restrictions are taken with respect to the given representations (μ, ξ) of T and (μ', ξ') of ∂T, which is Simon's 2.9 (T⌞A(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T) for any representation; A_t := T⌞{f < t}, B_t := (∂T)⌞{f < t}, Z_t := ∂A_t − B_t (= ⟨T, f, t₋⟩).

Notation: |α| is the Euclidean coefficient norm of a covector (covectorEuclideanNorm); |ω|_∞ := sup_x |ω(x)|. Elementary facts: (E1) for a 1-covector β and a k-covector γ, |β ∧ γ| ≤ |β||γ| (k!|γ|² = Σ_{i_1,…,i_k} γ(e_{i_1}, …, e_{i_k})² is the Hilbert–Schmidt norm of the multilinear form γ, independent of the orthonormal basis, so |·| is invariant under orthogonal changes of coordinates; rotate so that β = |β|e¹, then β∧γ = |β|Σ_{I∌1}γ_I e¹∧e^I); (E2) by hypothesis |ξ(x)(α)| ≤ |α| for μ-a.e. x and |ξ'(x)(α)| ≤ |α| for μ'-a.e. x.

Proof.
1. (The restricted currents exist.) For a Borel set E define A_E(ω) := ∫_E ξ(x)(ω(x)) dμ(x) for ω ∈ 𝒟^{k+1}(U). By (E2), |ξ(x)(ω(x))| ≤ |ω|_∞ 1_{tsupport ω}(x) μ-a.e., and tsupport ω is a compact subset of U, so μ(tsupport ω) < ∞ and the integrand is integrable (it is a.e. strongly measurable as the composition of the a.e. strongly measurable ξ with the continuous pairing). A_E is linear. If ω_j → 0 in 𝒟^{k+1}(U) (TestFormOnConverges: supports in a fixed compact K ⊆ U, uniform convergence of the forms and of all derivatives; |·| is equivalent to any norm on the finite-dimensional covector space), then |A_E(ω_j)| ≤ |ω_j|_∞ μ(K) → 0. So A_E ∈ 𝒟_{k+1}(U). Likewise B_E(η) := ∫_E ξ'(η) dμ' defines B_E ∈ 𝒟_k(U). Put A_t := A_{{f<t}}, B_t := B_{{f<t}} ({f < t} is open, f being continuous). These satisfy the first two conclusions. Note also T = A_{ℝ^P} and ∂T = B_{ℝ^P} by the representation hypotheses.

2. (Support of the slice.) Let η ∈ 𝒟^k(U) with tsupport η ∩ {f = t} = ∅. K := tsupport η is compact, so K = K₋ ∪ K₊ with K₋ := K ∩ {f < t} and K₊ := K ∩ {f > t} disjoint compact sets. Choose χ ∈ C^∞(ℝ^P; [0, 1]) with χ = 1 on a neighbourhood of K₋ and χ = 0 on a neighbourhood of K₊, and put η₋ := χη, η₊ := (1 − χ)η. Both are test forms in U, η = η₋ + η₊, and since η₋ vanishes near K₊ and outside K, tsupport η₋ ⊆ K₋ ⊆ {f < t}; similarly tsupport η₊ ⊆ K₊ ⊆ {f > t}. Then:
 (∂A_t)(η₊) = A_t(dη₊) = ∫_{f<t} ξ(dη₊) dμ = 0 and B_t(η₊) = ∫_{f<t} ξ'(η₊) dμ' = 0, because η₊ and dη₊ vanish on {f < t};
 (∂A_t)(η₋) = ∫_{f<t} ξ(dη₋) dμ = ∫ ξ(dη₋) dμ = T(dη₋) = ∂T(η₋) = ∫ ξ'(η₋) dμ' = ∫_{f<t} ξ'(η₋) dμ' = B_t(η₋), because η₋ and dη₋ vanish outside {f < t}.
Adding, (A_t).boundary η = B_t η, the third conclusion.

3. (Pointwise estimate, Simon 4.9 for Lipschitz f.) Fix t ∈ ℝ and an open W. Let 0 < h < 1 and ε := h²/8. Choose a C^∞ nonincreasing γ : ℝ → [0, 1] with γ = 1 on (−∞, t − h + ε], γ = 0 on [t − ε, ∞) and |γ'| ≤ 1/(h − 4ε) (mollify, at scale < ε, the piecewise linear function equal to 1 on (−∞, t − h + 2ε], to 0 on [t − 2ε, ∞) and linear in between). Let f_σ := f ∗ φ_σ (σ > 0, φ_σ a standard mollifier on ℝ^P): f_σ is C^∞, |∇f_σ| ≤ L everywhere and |f_σ − f| ≤ Lσ. For σ with Lσ < ε put g_σ := γ ∘ f_σ (C^∞, values in [0, 1], all derivatives bounded on compact sets) and g := γ ∘ f (continuous).
 (i) For η ∈ 𝒟^k(U): g_σ dη and g_ση are test forms in U and d(g_σ η) = dg_σ ∧ η + g_σ dη, so
 T(g_σ dη) − ∂T(g_σ η) = T(g_σ dη) − T(d(g_σ η)) = −T(dg_σ ∧ η).
 (ii) dg_σ(x) = γ'(f_σ(x)) df_σ(x) vanishes unless t − h + ε < f_σ(x) < t − ε, and then t − h < f(x) < t (as |f_σ − f| < ε); |dg_σ| ≤ L/(h − 4ε). By the representation of T, (E1) and (E2): if tsupport η ⊆ W and |η| ≤ 1, then |T(dg_σ ∧ η)| ≤ ∫ |dg_σ||η| dμ ≤ (L/(h − 4ε)) μ(W ∩ {t − h < f < t}).
 (iii) As σ ↓ 0, g_σ → g uniformly (γ is Lipschitz and f_σ → f uniformly), so by the representations, T(g_σ dη) → ∫ g ξ(dη) dμ and ∂T(g_σ η) → ∫ g ξ'(η) dμ' (dominated convergence on the compact set tsupport η, of finite μ- and μ'-measure). Hence for admissible η (tsupport η ⊆ W, |η| ≤ 1):
 ∫ g_h ξ(dη) dμ − ∫ g_h ξ'(η) dμ' ≤ (L/(h(1 − h/2))) μ(W ∩ {t − h < f < t}), where g_h := γ_h ∘ f records the dependence of γ on h, and h − 4ε = h(1 − h/2).
 (iv) As h ↓ 0, g_h → 1_{{f<t}} pointwise: if f(x) < t then f(x) ≤ t − h + ε for h ≤ t − f(x), so g_h(x) = 1; if f(x) ≥ t then f(x) ≥ t − ε and g_h(x) = 0. By dominated convergence, ∫ g_h ξ(dη) dμ → ∫_{f<t} ξ(dη) dμ = (∂A_t)(η) and ∫ g_h ξ'(η) dμ' → B_t(η). Taking the limit along a sequence h_i ↓ 0 realizing liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t}) (and using (1 − h/2)⁻¹ → 1) gives
 Z_t(η) = (∂A_t − B_t)(η) ≤ L · liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t})
for every admissible η. Hence M_W(Z_t) = sup ofReal(Z_t(η)) ≤ L · liminf_{h→0⁺} ofReal(h⁻¹) μ(W ∩ {t − h < f < t}) in [0, ∞], the fourth conclusion. (All inequalities in (ii)–(iv) may be read in [0, ∞]; the integrals involved are finite because only the compact set tsupport η matters, e.g. μ(W ∩ {t − h < f < t}) may be replaced by μ(tsupport η ∩ {t − h < f < t}) < ∞ in (ii). If L = 0 then f is constant, {t − h < f < t} = ∅ for small h, the bound in (ii) is 0 and Z_t = 0; so the ℝ≥0∞ convention 0·∞ = 0 causes no problem: when the liminf is ∞ we have L > 0 and the claim is trivial.)

4. (Integral estimate, Simon 4.10.) Fix an open W and a, b. If a ≥ b then Ioo a b = ∅ and there is nothing to prove; assume a < b. If L = 0, step 3 gives M_W(Z_t) = 0 for every t and the claim holds. If L > 0 and μ(W ∩ {a < f < b}) = ∞ there is nothing to prove. Otherwise let F(s) := μ(W ∩ {a < f < s}) for s ≤ b and F(s) := F(b) for s > b: a bounded nondecreasing real function on ℝ with F = 0 on (−∞, a]. For t ∈ (a, b) and 0 < h < t − a, {t − h < f < t} ⊆ {a < f < t} ∖ {a < f < t − h}, so μ(W ∩ {t − h < f < t}) ≤ F(t) − F(t − h). By Lebesgue's theorem (Mathlib Monotone.ae_differentiableAt), F is differentiable at a.e. t, and there step 3 gives M_W(Z_t) ≤ L F'(t). Hence (Mathlib lintegral_mono_ae; the lower Lebesgue integral needs no measurability of t ↦ M_W(Z_t)) ∫⁻_{(a,b)} M_W(Z_t) dt ≤ L ∫⁻_{(a,b)} F'(t) dt. Finally ∫_{(a,b)} F' ≤ F(b) − F(a) = μ(W ∩ {a < f < b}) by Mathlib MonotoneOn.intervalIntegral_deriv_mem_uIcc (F' = deriv F a.e. is nonnegative, it is integrable on [a, b] by Mathlib MonotoneOn.intervalIntegrable_deriv, and its interval integral lies in [0, F(b) − F(a)]); F(a) = 0. This is the fifth conclusion. ∎

## Key steps

1. The restricted currents exist (integrable integrands, sequential continuity from finiteness of μ, μ′ on compacts).
2. Support: split a test form disjoint from {f = t} into parts supported in {f < t} and {f > t}; on each part ∂A_t and B_t agree.
3. Pointwise bound: smooth cut-offs γ ∘ f_σ (f_σ a mollification of f) give ∂(T⌞g) − (∂T)⌞g = −T⌞(dg ∧ ·) with mass ≤ (L/h)μ(W ∩ {t − h < f < t}); let σ → 0 and h → 0.
4. Integral bound: the pointwise bound is ≤ L F′(t) for the monotone F(t) = μ(W ∩ {a < f < t}); integrate with MonotoneOn.intervalIntegral_deriv_mem_uIcc.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n 'cmc_|dtc_vanish_off_support' local-references/123e8435b4a2469b/project (no match); rg -c sorry local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match); rg -n 'theorem eLpNorm_le_eLpNorm_fderiv_one|theorem tendsto_measure_thickening_of_isClosed' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'federer|deformation|flat (norm|metric|convergence)|slice|slicing|closure theorem|boundary rectifiab' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06`
- `python3 scan of dag.json: lean_name, lean_statement, status and children of all 451 nodes; collisions of the twelve proposed names; accepted nodes with matching types (dtc_vanish_off_support, dor_ims_massOn_le_measure, dor_ims_measure_le_massOn, regcomp_approx_tangent_locality, regcomp_covector_eval_orthonormal_le, rsdic_unitOrientation_eq_or_eq_neg, dtc_isIntegerMultiplicity_sub); cross-branch reuse edges`
- `grep compactness_of_minimizing cluster-state/logs/gmt-ch07/*.log; comparison of swarm-configs/3cda86c657b24789a5e2370499838a03.json and e19a0116cbcc4eccb5496520b27c492f.json (max_nodes 200 vs 1000); node-directory timestamps at the v3 and v4 audit times`
- `sed -n 1300,1700p and 1801,2000p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; grep -n 'def ensure' -A 35 store.py`
- `grep for declarations simon_theorem_4_14_caratheodory, simon_theorem_4_14_positive_envelope, vectorFunctionalEnvelopeMeasure_isRadon, radonCaratheodoryMeasure_apply, integral_radonCaratheodoryMeasure, IsLocallyBoundedCcFunctional, simon_theorem_4_16_compact_metrizable, simon_theorem_3_6, simon_remark_3_7_hausdorff, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, simonHausdorffMeasureReal_toOuterMeasure, simon_theorem_3_3, simon_theorem_3_26_i, exists_isClosed_continuousOn_of_measurable, area_image_criticalSet_eq_zero, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, exteriorDerivativeOn_pullbackFormWithin, countablyRectifiable_of_measure_zero, HasApproximateTangentSpaceAt.unique, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, affinePushforward in lake-packages-25730c7c/simongmt/Poincare`
- `grep for declarations Monotone.ae_differentiableAt, measurable_deriv, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, LipschitzWith.ae_differentiableAt, LipschitzOnWith.hausdorffMeasure_image_le, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LinearMap.exists_antilipschitzWith, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.extend_real, LipschitzOnWith.extend_pi, Besicovitch.exists_disjoint_closedBall_covering_ae, VitaliFamily.ae_tendsto_average_norm_sub, isMulLeftInvariant_eq_smul, tendstoUniformlyOn_of_ae_tendsto, LipschitzWith.integral_lineDeriv_mul_eq, eLpNorm_le_eLpNorm_fderiv_one, euclideanHausdorffMeasure_zero, hausdorffMeasure_smul₀, tendsto_measure_thickening_of_isClosed, countable_meas_level_set_pos, Integrable.integral_eq_integral_meas_lt, SmoothPartitionOfUnity.exists_isSubordinate, exists_contDiff_tsupport_subset, ContDiffBump.normed, AlternatingMap.map_linearDependent, Vitali.exists_disjoint_subfamily_covering_enlargement, RealRMK.rieszMeasure, ext_of_generate_finite, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, hausdorffMeasure_zero_singleton, Besicovitch.tendsto_filterAt in lake-packages-25730c7c/mathlib/Mathlib`
- `lake env lean /tmp/cmc-a5/lean/TypesFinal.lean; lake env lean /tmp/cmc-a5/lean/AssemblyFinal.lean; lake env lean /tmp/cmc-a5/lean/Inst.lean; lake env lean /tmp/cmc-a5/lean/Names.lean; lake env lean /tmp/cmc-a5/lean/Names2.lean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD; git -C lake-packages-25730c7c/mathlib rev-parse HEAD`
- `sed -n 176,260p book/chapter-07.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-review-receipt-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/3cda86c657b24789a5e2370499838a03.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/e19a0116cbcc4eccb5496520b27c492f.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/3cda86c657b24789a5e2370499838a03.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/e19a0116cbcc4eccb5496520b27c492f.log`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/cmc-a5/final.json`
- `/tmp/cmc-a5/scripts/build_final.py`
- `/tmp/cmc-a5/scripts/gen_types_final.py`
- `/tmp/cmc-a5/scripts/gen_assembly.py`
- `/tmp/cmc-a5/scripts/body.lean`
- `/tmp/cmc-a5/lean/TypesFinal.lean`
- `/tmp/cmc-a5/lean/AssemblyFinal.lean`
- `/tmp/cmc-a5/lean/Inst.lean`
- `/tmp/cmc-a5/lean/Names.lean`
- `/tmp/cmc-a5/lean/Names2.lean`

The snapshot contract (manifest: project b4d606db, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean, and each snapshot chapter contract has only its frozen final sorry; the pinned packages are SimonGMT 2b366308 and Mathlib 25730c7c. SimonGMT Chapter06 says Federer–Fleming compactness remains a separate obligation and contains only point slices of products. Neither SimonGMT nor the snapshot Mathlib has a closure, deformation, Lipschitz-slicing or flat-convergence theorem (rg: no match). These results, Riesz representation and absolute continuity of normal currents, and IM calculus therefore remain children with complete parent-written proofs. Reusable library facts: WeaklyConvergesOn.massOn_le_liminf and WeaklyConvergesOn.boundary, the Chapter01 Riesz, compactness, density and Lusin theorems, the Chapter02 area formulas and the Chapter03 rectifiability API. Every SimonGMT and Mathlib declaration cited by name in the child proofs exists in the pinned sources. The 451-node DAG contains no cmc_ name, and the snapshot project has no cmc_ or dtc_ name. dtc_vanish_off_support is a comparator-accepted node whose frozen type equals the vanish_off_support child type, so it is reused verbatim; accepted declarations covering parts of mass_equals_rep_measure and im_calculus are named in remarks. In the workspace build, all 12 exact child types elaborate after import GMT.Ch07.Submission. The conditional assembly of CompactnessOfMinimizingCurrents from the six used child types depends only on propext, Classical.choice and Quot.sound, and current subtraction uses the contract instance. The identical previously accepted split was dropped only by the runtime node bound (max_nodes = 200 with about 200 DAG nodes); the current configuration allows 1000 nodes. Book lines 176–260 confirm the two corrections used in local_comparison.
