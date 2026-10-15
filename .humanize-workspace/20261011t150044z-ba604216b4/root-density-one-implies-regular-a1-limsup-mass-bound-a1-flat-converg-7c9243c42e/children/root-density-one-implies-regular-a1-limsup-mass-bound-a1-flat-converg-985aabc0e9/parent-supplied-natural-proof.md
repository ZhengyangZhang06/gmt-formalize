# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.product_imrep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3, where the product IMRep is R̂_X = ((0,1) × M, θ∘pr₂, e₀ ∧ ξ): (iii) rectifiability, (iv) the tangent planes ℝe₀ ⊕ T_xM oriented by e₀ ∧ ξ, and (v) the action formula by Fubini. The geometry of the cylinder is the sibling dor_lmb_fcdp_cylinder (CYL).
Notation: ι(t,x) := toLp(Fin.cons t (ofLp x)) ∈ ℝ^{P+1}, pr(y) := toLp(Fin.tail(ofLp y)) ∈ ℝ^P and y₀ := ofLp y 0. By definition pr(ι(t,x)) = x and (ι(t,x))₀ = t (rfl). ê₀ := EuclideanSpace.single 0 1 = ι(1,0) and J v := ι(0,v); J is a linear isometry, and ⟨ι(s,x), ι(s',x')⟩ = ss' + ⟨x,x'⟩, so ê₀ ⊥ J(ℝ^P). For a subspace Q ⊆ ℝ^P put Q̂ := span(insert ê₀ (J''Q)) = span{ê₀} ⊔ J(Q). For b ∈ ℝ^{k+1} write b₀ := ofLp b 0 and tail b := toLp(Fin.tail(ofLp b)) ∈ ℝ^k, and put π(b) := (b₀, tail b) ∈ ℝ × ℝ^k.
1. (Finiteness.) θ ≥ 1 on M, so H^k(M ∩ A) ≤ μ_R(A) for Borel A. In particular H^k(M) ≤ μ_R(ℝ^P) < ∞.
2. (Cylinder.) Apply (CYL) to M = R.carrier, which is Borel, countably k-rectifiable and of finite H^k-measure. It gives a Borel C ⊆ ι((0,1) × M) such that C is countably (k+1)-rectifiable, μHE[k+1]⌞C = ι_*(L¹⌞(0,1) ⊗ H^k⌞M), and the tangent transfer (CYL)(3) holds.
3. (Borel orientation.) ξ is AEStronglyMeasurable for H^k⌞M. Let ξ' be a strongly measurable function with ξ = ξ' H^k⌞M-a.e. (AEStronglyMeasurable.mk). Then R.action γ = ∫_M θ ξ'(γ) dH^k for every k-form γ (integral_congr_ae). By R.orients, the set N₀ := {x ∈ M : ¬∃ Q, HasApproximateTangentSpaceAt k M x Q ∧ IsUnitOrientationOf (ξ' x) Q} is H^k-null. For x ∈ M ∖ N₀, ‖ξ'(x)‖ ≤ 1, because |ξ'(x)(α)| = |α(τ)| ≤ ‖α‖∏‖τ_i‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm).
4. (Linear maps c and Ξ.) Let c : Λ^{k+1}(ℝ^{P+1}) →L Λ^k(ℝ^P), c(β) := (β.curryLeft ê₀).compContinuousLinearMap J. It is continuous linear with ‖c‖ ≤ 1. For ζ ∈ MultiVector P k put Ξ(ζ) := ζ ∘L c ∈ MultiVector (P+1) (k+1). Ξ is continuous linear and ‖Ξ(ζ)‖ ≤ ‖ζ‖.
5. (Definition.) R' has carrier C, multiplicity θ'(y) := θ(pr y) and orientation ξ̂(y) := Ξ(ξ'(pr y)).
6. (Consequences of (CYL)(2).) Using MeasurableEmbedding.lintegral_map / integral_map for ι and Tonelli/Fubini on the finite product measure:
   (6a) ∫⁻_C g dH^{k+1} = ∫_{(0,1)} ∫⁻_M g(ι(t,x)) dH^k(x) dt for measurable g ≥ 0.
   (6b) ∫_C f dH^{k+1} = ∫_M ∫_{(0,1)} f(ι(t,x)) dt dH^k(x) for f integrable w.r.t. H^{k+1}⌞C (integral_prod_symm or integral_integral_swap).
   (6c) If N ⊆ ℝ^P is Borel with H^k(M ∩ N) = 0, then H^{k+1}(C ∩ pr⁻¹N) = L¹((0,1))·H^k(M ∩ N) = 0. Hence a property that holds for H^k⌞M-a.e. x holds at pr y for H^{k+1}⌞C-a.e. y (enlarge the exceptional set to a Borel null set).
7. (IMRep fields.)
   measurableSet_carrier, carrier_subset and rectifiable: (CYL) and step 2.
   measurable_mult: θ' = θ ∘ pr.
   mult_pos: y ∈ C ⊆ ι((0,1) × M) gives pr y ∈ M, so θ'(y) = θ(pr y) > 0.
   locallyIntegrable_mult: ∫⁻_{C∩K} θ' dH^{k+1} ≤ ∫⁻_C θ∘pr dH^{k+1} = ∫_{(0,1)} ∫⁻_M θ dH^k dt = μ_R(ℝ^P) < ∞, by (6a).
   aestronglyMeasurable_orient: ξ̂ = Ξ ∘ ξ' ∘ pr is strongly measurable.
8. (orients.) By (6c) applied to a Borel null set containing N₀, for H^{k+1}⌞C-a.e. y we have pr y ∉ N₀. Intersect with the almost-everywhere statement (CYL)(3). Fix such a y and put x := pr y ∈ M. There is Q with HasApproximateTangentSpaceAt k M x Q and IsUnitOrientationOf (ξ' x) Q, i.e. an orthonormal τ = (τ_1, …, τ_k) with span τ = Q and ξ'(x)(α) = ±α(τ) (fixed sign).
   By (CYL)(3), C has approximate tangent space Q̂ at y.
   For β ∈ Λ^{k+1}(ℝ^{P+1}): ξ̂(y)(β) = ξ'(x)(c(β)) = ±c(β)(τ) = ±β(τ̂), where τ̂ := Fin.cons ê₀ (J ∘ τ). Here use ContinuousAlternatingMap.curryLeft_apply_apply and compContinuousLinearMap_apply, with Matrix.vecCons = Fin.cons.
   τ̂ is orthonormal, since J is isometric and ê₀ is a unit vector orthogonal to J(ℝ^P). Also span τ̂ = span(insert ê₀ (J''(span τ))) = Q̂. Hence IsUnitOrientationOf (ξ̂ y) Q̂, and the orients field holds at y.
9. (Conclusion (1).) μ_{R'}(ℝ^{P+1}) = ∫⁻_C θ∘pr dH^{k+1} = μ_R(ℝ^P) < ∞, by (6a).
10. (Conclusion (2).) Let S be Borel with H^k(M ∖ S) = 0. If y ∈ C ∖ ι([0,1] × S), then y = ι(t,x) with t ∈ (0,1) and x ∈ M ∖ S, so pr y ∈ ℝ^P ∖ S. Hence H^{k+1}(C ∖ ι([0,1] × S)) ≤ H^{k+1}(C ∩ pr⁻¹(ℝ^P ∖ S)) = L¹((0,1))·H^k(M ∖ S) = 0, by (6c).
11. (Conclusion (3).) Let β be continuous with ‖β(y)‖ ≤ C_β. Put f(y) := θ'(y)ξ̂(y)(β(y)), which is measurable. For H^{k+1}⌞C-a.e. y, |f(y)| ≤ θ(pr y)·‖ξ'(pr y)‖·‖c‖·‖β(y)‖ ≤ C_β·θ(pr y), by step 3 and (6c). The bound is integrable by (6a). By (6b), R'.action β = ∫_C f dH^{k+1} = ∫_M θ(x) ∫_{(0,1)} ξ'(x)(c(β(ι(t,x)))) dt dH^k(x).
   ξ'(x) is continuous linear and t ↦ c(β(ι(t,x))) is continuous, so the inner integral is ξ'(x)(∫_0^1 c(β(ι(t,x))) dt) (ContinuousLinearMap.intervalIntegral_comp_comm). The set integral over (0,1) equals the interval integral over [0,1], since Ioc and Ioo differ by a null set (intervalIntegral.integral_of_le).
   Using ξ = ξ' a.e., R'.action β = ∫_M θ(x) ξ(x)(∫_0^1 c(β(ι(t,x))) dt) dH^k(x). Finally fderiv ℝ (x' ↦ ι(t,x')) x = J, since x' ↦ ι(t,x') = ι(t,0) + Jx' is affine. So this is R.action(x ↦ ∫_0^1 (β(ι(t,x)).curryLeft ê₀) ∘ D_xι(t,x) dt). ∎

## Key steps

1. Apply the cylinder lemma to M = R.carrier to get a Borel rectifiable C ⊆ ι((0,1)×M) with H^{k+1}⌞C = ι_*(L¹⌞(0,1) ⊗ H^k⌞M) and tangent planes Q̂ = ℝê₀ ⊕ J(Q).
2. R′ := (C, θ∘pr, Ξ(ξ′∘pr)) with ξ′ a Borel version of ξ and Ξ(ζ)(β) = ζ((β.curryLeft ê₀)∘J); measure identity gives finiteness, local integrability and null-set transfer.
3. orients: transfer R.orients to a.e. y ∈ C; e₀ followed by J of an orthonormal basis of Q is an orthonormal basis of Q̂ realizing Ξ(ξ′(pr y)).
4. A.e.-containment in ι([0,1]×S) and the action formula with the t-integral inside R.action by Fubini.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical)`
- `rg -n 'theorem extDeriv_pullback|analyticOnNhd_compContinuousLinearMapCLM|theorem dist_convolution_le|theorem volume_preserving_piFinSuccAbove|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le|theorem curryLeft_compContinuousLinearMap|theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul|Filter.EventuallyEq.extDeriv_eq|theorem det_succ_row_zero' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'measure_compl_support|theorem integral_comp_comm|theorem integral_eq_sub_of_hasDerivAt|theorem norm_fderiv_le_of_lipschitz' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'pushforward|homotop|cartan|curryLeft|dor_lmb_fcdp' local-references/123e8435b4a2469b/project/GMT -g '*.lean' (only sorry-frozen Ch06 IsLipschitzPushforward/LipschitzPushforwardIntegerMultiplicity and Ch07 affinePushforward; no Lipschitz push-forward, product current, homotopy formula or Cartan theorem)`
- `grep -n 'def |theorem ' SimonGMT Chapter06/{Forms,Currents,Mass,WedgeForms,Product,GeometricPointProduct,CurrentLocalEquality}.lean, Chapter03/Rectifiable.lean, Chapter02/AreaLipschitz.lean`
- `lake env lean Avail.lean/Avail2.lean/Avail3.lean/Elab.lean: #check every cited Mathlib/SimonGMT lemma after import GMT.Ch07.Submission (unavailable: ContDiffBump.normed, intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le, SimonGMT Chapter02 area formulas, Matrix.det_gram_ne_zero_iff_linearIndependent)`
- `python3 -I scans of dag.json: status/frozen types of dor_lmb_fcd_im_pushforward (decomposing), dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, covectorEuclideanNorm_gram_bounds, dpf_exists_orthonormal_frame_det_gram, dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, codim1_lura_gram_area_formula (accepted, byte-identical), cmcdt_lipschitz_pushforward_homotopy subtree (not accepted); regex searches for Hadamard, area-formula and mollification lemmas; freshness of dor_lmb_fcdp_* names`
- `git show a95facf7331f:GMT/Ch07/Submission.lean (accepted dpf_pb_smooth_pullback_isTestForm: analyticOnNhd_compContinuousLinearMapCLM + ContDiff.clm_apply)`
- `sed runtime.py (_decompose max_depth, _existing_lean_name_problem, _overlay_accepted_children) and verifier/gmt-compare.py contract_scope`
- `lake env lean /tmp/pfc-decomp-k7q2/lean/AllTypes.lean and Assembly.lean with #print axioms; python3 /tmp/pfc-decomp-k7q2/py/cartan_check2.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-7c9243c42e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/pfc-decomp-k7q2/lean/AllTypes.lean`
- `/tmp/pfc-decomp-k7q2/lean/Assembly.lean`
- `/tmp/pfc-decomp-k7q2/py/cartan_check2.py`

The snapshot (project b4d606db, mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace one. Neither the snapshot nor SimonGMT has a proved Lipschitz push-forward of currents, product current, homotopy formula or Cartan formula. SimonGMT Chapter06 offers only affine push-forwards and point products, and the snapshot's Ch06 Lipschitz push-forward is a sorry-frozen definition outside the import closure. The import closure of GMT.Ch07.Submission lacks SimonGMT Chapter02 area formulas, ContDiffBump.normed and intervalIntegral parametric derivatives. It has every Mathlib lemma the child proofs cite (all located in the snapshot mathlib): extDeriv_pullback, EventuallyEq.extDeriv_eq, analyticOnNhd_compContinuousLinearMapCLM, curryLeft_compContinuousLinearMap, hasFDerivAt_integral_of_dominated_of_fderiv_le, dist_convolution_le, contDiff_convolution_left, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, det_succ_row_zero, measure_compl_support, euclideanHausdorffMeasure_eq_volume, integral_eq_sub_of_hasDerivAt. The missing area formula and Hadamard and piece facts come from six comparator-accepted DAG declarations reused with byte-identical types. IPF is unaccepted, so it is passed as an exact-type antecedent and discharged by this node with Submission.dor_lmb_fcd_im_pushforward hIMS. All 12 child types compile as exact challenges. The conditional assembly proves this node's frozen type with axioms [propext, Classical.choice, Quot.sound]. The six new dor_lmb_fcdp_* names are fresh in dag.json.
