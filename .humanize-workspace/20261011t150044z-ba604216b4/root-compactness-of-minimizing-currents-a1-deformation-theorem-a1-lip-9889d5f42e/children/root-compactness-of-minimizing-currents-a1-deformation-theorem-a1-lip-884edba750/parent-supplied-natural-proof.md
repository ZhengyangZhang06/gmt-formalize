# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 1 ((L0)–(L3)), specialized and completed. No hypotheses or dependencies are used.

Notation. e_1, …, e_N is the standard orthonormal basis of ℝ^N = Euclid N (EuclideanSpace.basisFun). For a k-covector α on ℝ^N, |α| := covectorEuclideanNorm α = (Σ_J α(e_{J(1)}, …, e_{J(k)})²)^{1/2}, the sum running over the strictly increasing J : Fin k → Fin N. For an orthonormal basis f = (f_1, …, f_N) of ℝ^N and a k-multilinear map γ : (ℝ^N)^k → ℝ put S_f(γ) := Σ_{I : Fin k → Fin N} γ(f_{I(1)}, …, f_{I(k)})² (all index tuples). |α| is the Euclidean norm of the coefficient vector (α(e_J))_J, which depends linearly on α; hence |cα| = |c||α|.

1. Basis independence of S. Let f, f' be orthonormal bases and γ k-multilinear. Write f_i = Σ_a O_{ai} f'_a with O_{ai} := ⟨f'_a, f_i⟩; O is orthogonal, so Σ_i O_{ai} O_{bi} = δ_{ab}. By multilinearity γ(f_{I(1)}, …, f_{I(k)}) = Σ_{a ∈ [N]^k} (Π_m O_{a_m I(m)}) γ(f'_{a_1}, …, f'_{a_k}). Squaring and summing over I gives S_f(γ) = Σ_{a,b} γ(f'_a) γ(f'_b) Π_m (Σ_i O_{a_m i} O_{b_m i}) = Σ_{a,b} γ(f'_a) γ(f'_b) Π_m δ_{a_m b_m} = S_{f'}(γ).

2. (L0) For alternating α and every orthonormal basis f, S_f(α) = k!·|α|². By step 1 it suffices to take f = e. If I takes some value twice then α(e_I) = 0. Every injective I factors uniquely as I = J∘σ with J strictly increasing and σ a permutation of Fin k, and α(e_{J∘σ}) = sign(σ)·α(e_J). Hence S_e(α) = Σ_J Σ_σ α(e_J)² = k!·|α|². (For k = 0 both sides are the square of the single value of α, and 0! = 1.)

3. (L3) Let τ_1, …, τ_k be orthonormal in ℝ^N. They are linearly independent, so k ≤ N, and they extend to an orthonormal basis f of ℝ^N with f_m = τ_m for m ≤ k (Mathlib Orthonormal.exists_orthonormalBasis_extension_of_card_eq / Gram–Schmidt). Among the tuples counted in S_f(α) are the k! tuples I = σ, σ a permutation of {1, …, k}; each contributes α(τ_{σ(1)}, …, τ_{σ(k)})² = (sign σ · α(τ))² = α(τ)². All other terms are ≥ 0. Hence k!|α|² = S_f(α) ≥ k!·α(τ)², i.e. |α(τ_1, …, τ_k)| ≤ |α|.

4. One-slot estimate. Let A : ℝ^N → ℝ^{N'} be continuous linear, e' the standard basis of ℝ^{N'} and β a k-covector on ℝ^{N'}. For 0 ≤ j ≤ k let γ_j(w_1, …, w_j, u_{j+1}, …, u_k) := β(Aw_1, …, Aw_j, u_{j+1}, …, u_k) (w's in ℝ^N, u's in ℝ^{N'}) and T_j := Σ γ_j(e_{I(1)}, …, e_{I(j)}, e'_{I(j+1)}, …, e'_{I(k)})², the sum over I(1), …, I(j) ∈ [N] and I(j+1), …, I(k) ∈ [N']. Claim: T_j ≤ ‖A‖²·T_{j−1} for 1 ≤ j ≤ k. Fix all indices except the j-th. The map u ↦ γ_{j−1}(…, u (in slot j), …) is a linear functional on ℝ^{N'}, of the form u ↦ ⟨g, u⟩. Then Σ_{i ∈ [N]} γ_j(…, e_i, …)² = Σ_i ⟨g, Ae_i⟩² = Σ_i ⟨A*g, e_i⟩² = |A*g|² ≤ ‖A*‖²|g|² = ‖A‖² Σ_{i' ∈ [N']} ⟨g, e'_{i'}⟩² = ‖A‖² Σ_{i'} γ_{j−1}(…, e'_{i'}, …)². Summing over the fixed indices proves the claim.

5. (L1) A^#β := β.compContinuousLinearMap A is alternating with A^#β(w) = β(Aw_1, …, Aw_k). By step 2, T_0 = S_{e'}(β) = k!|β|² and T_k = S_e(A^#β) = k!|A^#β|². By step 4, T_k ≤ ‖A‖^{2k} T_0, so |A^#β|² ≤ ‖A‖^{2k}|β|², and taking square roots of nonnegative numbers gives covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖^k · covectorEuclideanNorm β. (For k = 0, A^#β = β and ‖A‖^0 = 1.)

6. (L2) Let v ∈ ℝ^N and β a (k+1)-covector. ι_vβ := β.curryLeft v satisfies ι_vβ(w_1, …, w_k) = β(v, w_1, …, w_k) (Mathlib ContinuousAlternatingMap.curryLeft_apply_apply; Matrix.vecCons v w = Fin.cons v w). If v = 0 then ι_vβ = 0 and both sides are 0. Otherwise put f_1 := v/|v|; then ι_vβ = |v|·ι_{f_1}β, and by homogeneity it suffices to show |ι_{f_1}β| ≤ |β|. Extend f_1 to an orthonormal basis f (as in step 3). By step 2 in the basis f: k!|ι_{f_1}β|² = Σ_{I ∈ [N]^k} β(f_1, f_{I(1)}, …, f_{I(k)})² and (k+1)!|β|² = Σ_{I' ∈ [N]^{k+1}} β(f_{I'})². In the second sum keep only the tuples I' in which the index 1 occurs exactly once (the dropped terms are ≥ 0). Such an I' is determined by the position p ∈ {0, …, k} of the index 1 and the tuple I ∈ ([N]∖{1})^k of the remaining entries, and β(f_{I'}) = ±β(f_1, f_I) (moving f_1 to the front permutes the arguments). Hence (k+1)!|β|² ≥ (k+1)·Σ_{I ∈ ([N]∖{1})^k} β(f_1, f_I)² = (k+1)·Σ_{I ∈ [N]^k} β(f_1, f_I)² (a term with some I(m) = 1 vanishes because β is alternating) = (k+1)·k!·|ι_{f_1}β|². Dividing by (k+1)! gives |ι_{f_1}β|² ≤ |β|². This proves all three conjuncts. ∎

## Key steps

1. Basis independence of the Hilbert–Schmidt sum S_f(γ) over orthonormal bases.
2. (L0): S_f(α) = k!·|α|² for alternating α (injective index tuples factor through increasing ones).
3. (L3): extend τ to an orthonormal basis; the k! permutations of τ contribute k!·α(τ)² ≤ k!|α|².
4. One-slot estimate T_j ≤ ‖A‖²T_{j−1}, iterated k times, gives (L1).
5. (L2): rotate v to a basis vector and compare the Hilbert–Schmidt sums of ι_{f_1}β and β.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest.json)`
- `rg -n 'cmcdt_lp' project mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n -i 'lipschitz.*push|pushforward|homotopy|LipschitzPushforward' project/GMT -g '*.lean'`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm|polyhedral chain' mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'noncomputable def curryLeft|theorem curryLeft_apply_apply' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem LipschitzWith.ae_differentiableAt|theorem LinearMap.exists_antilipschitzWith|theorem integral_lineDeriv_mul_eq|theorem ae_convolution_tendsto_right_of_locallyIntegrable|theorem Orthonormal.exists_orthonormalBasis_extension|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|lemma tendsto_tsum_of_dominated_convergence|theorem volume_preserving_piFinSuccAbove|theorem exists_contDiff_tsupport_subset|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le|theorem _root_.MeasurableSet.exists_isCompact_lt_add' mathlib/Mathlib -g '*.lean' (all found)`
- `grep -rn for measurableSet_of_differentiableAt, measurable_fderiv, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, ContDiffBump.normed, HasCompactSupport.contDiff_convolution_left, intervalIntegral.integral_eq_sub_of_hasDerivAt, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp in the pinned Mathlib (all found)`
- `grep in lake-packages-25730c7c/simongmt/Poincare/SimonGMT (Chapter06 Currents/Mass/CurrentLocalEquality/Forms/AffineCurrentPushforward/Product, Chapter03/Rectifiable, Chapter02/AreaDomain/AreaCritical): GeometricCurrentOn, massOn, support, boundary, boundary_boundary, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, exteriorDerivative_apply, exteriorDerivativeOn_pullbackFormWithin, tsupport_exteriorDerivative_subset, affinePullbackTestOn, TestFormOnConverges.affinePullback, CountablyRectifiable, countablyRectifiable_range, countablyRectifiable_of_measure_zero, HasApproximateTangentSpaceAt.unique, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, area_image_criticalSet_eq_zero (all found)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: frozen types of the selected node, its siblings and cmcdt_im_series; lean_name scan for push/homot/covector/tangent/rectifiable lemmas; accepted covectorEuclideanNorm and HasApproximateTangentSpaceAt declarations; no name with prefix cmcdt_lp_`
- `grep of the controller (runtime/flows/*/_recursive_lean/runtime.py: _existing_lean_name_problem, _install_parent_supplied_child_handoff, _overlay_accepted_children) for the cross-branch reuse semantics`
- `lake env lean /tmp/lpdecomp/lean/T_L.lean, T_O.lean, T_I.lean (child types elaborate); lake env lean /tmp/lpdecomp/lean/Interface.lean (instance checks and interface derivation; axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/lpdecomp/lean/AssemblyFull.lean (sorry-free Part C assembly from the IMS, operators and integrality types to the exact selected frozen type; axioms propext, Classical.choice, Quot.sound)`
- `sed -n 360,620p and 760,900p book/chapter-06.txt (Simon 6.2.17–2.33 and 6.3.3–3.12, the source of Parts A and B)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lpdecomp/lean/T_L.lean`
- `/tmp/lpdecomp/lean/T_O.lean`
- `/tmp/lpdecomp/lean/T_I.lean`
- `/tmp/lpdecomp/lean/Interface.lean`
- `/tmp/lpdecomp/lean/AssemblyFull.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Contract.lean and Submission.lean. Its only Lipschitz push-forward material is the unsolved Ch06 specification (project/GMT/Ch06/Contract.lean and Submission.lean: IsLipschitzPushforward, LipschitzPushforwardIntegerMultiplicity; main_theorem := by sorry). It is written over a different Euclidean type (Eucl), cannot be imported into Ch07 and contains no proofs, so nothing in it is reusable. Mathlib has no flat-norm, deformation or polyhedral-chain results (no match). It does provide every tool cited by the child proofs: curryLeft as interior product, Rademacher, the approximately-linear partition, antilipschitz bounds for injective maps, mollification with a.e. convergence of derivatives, density and Lebesgue points, inner regularity, differentiation under interval integrals, the Fubini splitting of volume on Euclid (n+1), and Tannery's theorem. SimonGMT provides currents, mass, support, weak convergence with lower semicontinuity of mass, the exterior-derivative and pull-back formulas, affine pull-back of test forms, rectifiability, approximate tangent spaces with uniqueness, and the area formulas. No DAG node, snapshot file or Mathlib declaration uses the prefix cmcdt_lp_. All three child types elaborate. The interface derivation compiles with axioms propext, Classical.choice and Quot.sound. The sorry-free Part C assembly compiles to the exact selected frozen type with axioms propext, Classical.choice and Quot.sound.
