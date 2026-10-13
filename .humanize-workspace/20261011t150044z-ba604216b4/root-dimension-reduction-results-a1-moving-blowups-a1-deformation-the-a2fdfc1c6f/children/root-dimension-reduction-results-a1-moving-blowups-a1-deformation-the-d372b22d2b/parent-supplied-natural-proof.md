# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 1 ((L0)–(L2), Simon Ch. 6 §1), specialized and completed. No hypotheses and no sibling results are used.

Notation. e_1, …, e_N is the standard orthonormal basis of ℝ^N = Euclid N (EuclideanSpace.basisFun). For a k-covector α on ℝ^N, |α| := covectorEuclideanNorm α = (Σ_J α(e_{J(1)}, …, e_{J(k)})²)^{1/2}, the sum over the strictly increasing J : Fin k → Fin N. |α| is the Euclidean norm of the coefficient vector (α(e_J))_J, which depends linearly on α, so |cα| = |c|·|α|. For an orthonormal basis f = (f_1, …, f_N) of ℝ^N and a k-multilinear map γ : (ℝ^N)^k → ℝ put S_f(γ) := Σ_{I : Fin k → Fin N} γ(f_{I(1)}, …, f_{I(k)})² (all index tuples). ‖A‖ is the operator norm and |v| the Euclidean norm.

1. Basis independence of S. Let f, f' be orthonormal bases of ℝ^N and γ k-multilinear. Write f_i = Σ_a O_{ai} f'_a with O_{ai} := ⟨f'_a, f_i⟩. O is an orthogonal matrix, so Σ_i O_{ai} O_{bi} = δ_{ab}. By multilinearity, γ(f_{I(1)}, …, f_{I(k)}) = Σ_{a ∈ [N]^k} (Π_m O_{a_m I(m)}) γ(f'_{a_1}, …, f'_{a_k}). Squaring and summing over I gives S_f(γ) = Σ_{a,b ∈ [N]^k} γ(f'_a) γ(f'_b) Π_m (Σ_i O_{a_m i} O_{b_m i}) = Σ_{a,b} γ(f'_a) γ(f'_b) Π_m δ_{a_m b_m} = S_{f'}(γ).

2. (L0) For an alternating k-covector α and every orthonormal basis f, S_f(α) = k!·|α|². By step 1 it suffices to take f = e. If I takes some value twice, then α(e_I) = 0. Every injective I : Fin k → Fin N factors uniquely as I = J∘σ with J strictly increasing and σ a permutation of Fin k, and α(e_{J∘σ}) = sign(σ)·α(e_J). Hence S_e(α) = Σ_J Σ_σ α(e_J)² = k!·|α|². (For k = 0 both sides equal the square of the single value of α, and 0! = 1.)

3. One-slot estimate. Let A : ℝ^N → ℝ^{N'} be continuous linear, e' the standard basis of ℝ^{N'} and β a k-covector on ℝ^{N'}. For 0 ≤ j ≤ k let γ_j(w_1, …, w_j, u_{j+1}, …, u_k) := β(Aw_1, …, Aw_j, u_{j+1}, …, u_k) (w's in ℝ^N, u's in ℝ^{N'}) and T_j := Σ γ_j(e_{I(1)}, …, e_{I(j)}, e'_{I(j+1)}, …, e'_{I(k)})², the sum over I(1), …, I(j) ∈ [N] and I(j+1), …, I(k) ∈ [N']. Claim: T_j ≤ ‖A‖²·T_{j−1} for 1 ≤ j ≤ k. Fix all indices except the j-th. The map u ↦ γ_{j−1}(…, u (in slot j), …) is a linear functional on ℝ^{N'}, hence of the form u ↦ ⟨g, u⟩ for some g ∈ ℝ^{N'}, and γ_j(…, e_i (in slot j), …) = ⟨g, Ae_i⟩. Then Σ_{i ∈ [N]} ⟨g, Ae_i⟩² = Σ_i ⟨A*g, e_i⟩² = |A*g|² ≤ ‖A*‖²|g|² = ‖A‖²·Σ_{i' ∈ [N']} ⟨g, e'_{i'}⟩² = ‖A‖²·Σ_{i'} γ_{j−1}(…, e'_{i'}, …)². Summing over the fixed indices proves the claim.

4. (L1) A^#β := β.compContinuousLinearMap A is an alternating k-covector on ℝ^N with A^#β(w_1, …, w_k) = β(Aw_1, …, Aw_k). By step 2, T_0 = S_{e'}(β) = k!·|β|² and T_k = S_e(A^#β) = k!·|A^#β|². Iterating step 3, T_k ≤ ‖A‖^{2k}·T_0, so |A^#β|² ≤ ‖A‖^{2k}|β|², and taking square roots of nonnegative numbers gives covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖^k · covectorEuclideanNorm β. (For k = 0, A^#β = β and ‖A‖^0 = 1.)

5. (L2) Let v ∈ ℝ^N and β a (k+1)-covector on ℝ^N. ι_vβ := β.curryLeft v is the k-covector with ι_vβ(w_1, …, w_k) = β(v, w_1, …, w_k) (Mathlib ContinuousAlternatingMap.curryLeft_apply_apply; Matrix.vecCons v w = Fin.cons v w), and it is linear in v. If v = 0 then ι_vβ = 0 and both sides are 0. Otherwise put f_1 := v/|v|; then ι_vβ = |v|·ι_{f_1}β, and by homogeneity of |·| it suffices to show |ι_{f_1}β| ≤ |β|. Extend f_1 to an orthonormal basis f = (f_1, …, f_N) of ℝ^N (Gram–Schmidt; Mathlib Orthonormal.exists_orthonormalBasis_extension). By step 2 in the basis f: k!·|ι_{f_1}β|² = Σ_{I ∈ [N]^k} β(f_1, f_{I(1)}, …, f_{I(k)})² and (k+1)!·|β|² = Σ_{I' ∈ [N]^{k+1}} β(f_{I'(0)}, …, f_{I'(k)})². In the second sum keep only the tuples I' in which the index 1 occurs exactly once (the dropped terms are ≥ 0). Such an I' is determined by the position p ∈ {0, …, k} of the index 1 and the tuple I ∈ ([N]∖{1})^k of the remaining entries in order, and β(f_{I'}) = ±β(f_1, f_I) (moving f_1 to the front permutes the arguments). Hence (k+1)!·|β|² ≥ (k+1)·Σ_{I ∈ ([N]∖{1})^k} β(f_1, f_I)² = (k+1)·Σ_{I ∈ [N]^k} β(f_1, f_I)² (a term with some I(m) = 1 vanishes because β is alternating) = (k+1)·k!·|ι_{f_1}β|². Dividing by (k+1)! gives |ι_{f_1}β|² ≤ |β|², hence |ι_vβ| ≤ |v|·|β|.

Steps 4 and 5 are the two conjuncts. ∎

## Key steps

1. Basis independence of the Hilbert–Schmidt sum S_f over orthonormal bases.
2. (L0): S_f(α) = k!·|α|² for alternating α.
3. One-slot estimate T_j ≤ ‖A‖²T_{j−1}; iterating k times gives (L1).
4. (L2): normalize v, extend v/|v| to an orthonormal basis and compare the Hilbert–Schmidt sums of ι_{f_1}β and β.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git rev-parse HEAD of the workspace (b4d606db) and of SNAPSHOT/mathlib (25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical)`
- `rg -c "dimred_mbl_dt_lp" SNAPSHOT lake-packages-25730c7c/simongmt (no match); python3 scan of RUN/dag.json lean_names for the six new names (none) and for the three reused names (accepted nodes with byte-identical lean_statement)`
- `rg -n -i "lipschitz.*push|pushforward.*lipschitz|weak continuity|jacobian.*weak|cylinder|\[\[0, ?1\]\]" SNAPSHOT/project/GMT -g "*.lean" (only the unproved Ch06 specification IsLipschitzPushforward / LipschitzPushforwardIntegerMultiplicity in Ch06/Contract.lean; Ch07 does not import Ch06)`
- `python3 scans of accepted RUN/dag.json lean_statements for covectorEuclideanNorm, curryLeft, compContinuousLinearMap, HasApproximateTangentSpaceAt, CountablyRectifiable, LipschitzWith, Orthonormal, ApproximatesLinearOn/AntilipschitzWith (found covectorEuclideanNorm_gram_bounds, regcomp_covector_eval_orthonormal_le, dpf_rectifiable_bilipschitz_pieces, ptd_piece_image_approxTangent_ae, dpf_approxTangent_ae_bilipschitz_piece; no Lipschitz push-forward, cylinder, Jacobian weak continuity or map-partition lemma)`
- `grep of SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap, HasApproximateTangentSpaceAt.unique, countablyRectifiable_range, CountablyRectifiable.mono, countablyRectifiable_of_measure_zero), Chapter06 Currents/Mass/CurrentLocalEquality/Forms (GeometricCurrentOn, boundary, ext, boundary_boundary, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn, WeaklyConvergesOn.boundary, covectorEuclideanNorm, massOn, mass, le_massOn, massOn_le_liminf, support, zeroRegion, exteriorDerivative_apply, exteriorDerivativeOn_pullbackFormWithin), Chapter02 AreaDomain/AreaCritical (injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, area_image_criticalSet_eq_zero, areaJacobianWithin)`
- `grep -rnE "(theorem|lemma) ..." SNAPSHOT/mathlib/Mathlib for exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, PiLp.volume_preserving_ofLp, volume_preserving_piFinSuccAbove, lipschitz_infDist_pt, infDist_zero_of_mem, hausdorffMeasure_image_le, MeasurableSet.image_of_continuousOn_injOn, tendsto_tsum_of_dominated_convergence, integral_lineDeriv_mul_eq, ae_convolution_tendsto_right_of_locallyIntegrable, measurableSet_of_differentiableAt, measurable_fderiv, LinearMap.exists_antilipschitzWith, ae_tendsto_measure_inter_div_of_measurableSet, ae_tendsto_average_norm_sub, Orthonormal.exists_orthonormalBasis_extension (all found)`
- `python3/cat of the twin node root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1 decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json and decomposition-scope-v1.json; sentence diff of the two parent-supplied proofs`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _accepted_checkpoint, _install_parent_supplied_child_handoff, _overlay_accepted_children) and store.py ensure; verifier gmt-compare.py contract_scope/child_modules; both validate_lean_statement implementations on all nine types`
- `lake env lean /tmp/dmlp/lean/Types.lean, /tmp/dmlp/lean/Challenge_<key>.lean for all nine keys (only sorry warnings), /tmp/dmlp/lean/Assembly.lean (#print axioms GMT.Ch07.DmlpAsm.assembly: propext, Classical.choice, Quot.sound), /tmp/dmlp/lean/Reexport.lean, /tmp/dmlp/lean/InstCheck.lean (clean)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dmlp/lean/Types.lean`
- `/tmp/dmlp/lean/Assembly.lean`
- `/tmp/dmlp/lean/Reexport.lean`
- `/tmp/dmlp/lean/InstCheck.lean`

Pins match: project b4d606db, Mathlib 25730c7c, and the workspace Submission is byte-identical to the frozen Ch07 contract. Neither the snapshot project nor Mathlib nor SimonGMT contains a Lipschitz push-forward of currents, a product with [[0,1]], or a weak-continuity lemma for Jacobians; the snapshot's Ch06 push-forward specification is unproved and not imported by Ch07. So covector_bounds, cylinder, operators, jacobian_continuity, im_pushforward and im_cylinder are new obligations under fresh, unused names (dimred_mbl_dt_lp_*). Three needed steps already exist as accepted DAG declarations with exactly the required types and are reused verbatim: covectorEuclideanNorm_gram_bounds (L3), dpf_rectifiable_bilipschitz_pieces (B1) and ptd_piece_image_approxTangent_ae (B2). Every cited Mathlib and SimonGMT name exists. All nine types elaborate in the comparator's challenge form and pass both validators. A Lean assembly derives the exact selected type from the operators, im_pushforward, im_cylinder and IMS types, using only propext, Classical.choice and Quot.sound.
