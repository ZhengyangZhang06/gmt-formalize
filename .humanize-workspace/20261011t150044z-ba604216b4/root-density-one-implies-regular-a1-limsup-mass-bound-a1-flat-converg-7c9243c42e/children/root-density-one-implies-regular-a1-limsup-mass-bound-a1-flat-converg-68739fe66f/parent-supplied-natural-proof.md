# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.smooth_homotopy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 7(b): Cartan's homotopy formula for the smooth homotopy h_j, which is Simon's derivation of 2.25 from 2.21–2.22 written on forms. Also the smoothness facts of steps 2, 4 and 7: the forms F_j^#ω and K_jω are smooth, so cut-offs of them are test forms. Mathlib conventions: extDeriv γ x v = Σ_{i=0}^{n} (−1)^i (Dγ(x)[v_i])(v_0, …, v̂_i, …, v_n) (extDeriv_apply); β.curryLeft u (w) = β(Fin.cons u w); (β.compContinuousLinearMap L)(w) = β(L ∘ w). The identity of (b) was checked numerically with exactly these conventions (k = 0, 1, 2, random smooth F, G, ω on ℝ³).
Part (a).
1. The map L ↦ compContinuousLinearMapCLM L, from L(ℝ^N, ℝ^{N'}) to Λ^m(ℝ^{N'}) →L Λ^m(ℝ^N), is analytic (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ), hence C^∞. The map x ↦ DΦ(x) is C^∞ (contDiff_infty_iff_fderiv), and x ↦ α(Φ x) is C^∞ (composition). Since Φ^#α(x) = compContinuousLinearMapCLM(DΦ(x))(α(Φ x)), Φ^#α is C^∞ by ContDiff.clm_apply. This is the argument of the accepted proof of dpf_pb_smooth_pullback_isTestForm.
Part (b). Notation: Z := ℝ × ℝ^P (product normed space) and e := (1, 0) ∈ Z. Let H : Z → ℝ^P, H(t, x) := F(x) + t•(G(x) − F(x)). For t ∈ ℝ let j_t : ℝ^P → Z, j_t(x) := (t, x), whose derivative is the constant J := ContinuousLinearMap.inr ℝ ℝ ℝ^P. Put V(x) := G(x) − F(x), A(t,x) := DF(x) + t•(DG(x) − DF(x)) and h(t,x) := H(t,x).
2. H is C^∞ with DH(t,x)(s, v) = s•V(x) + A(t,x)v. In particular DH(t,x) e = V(x) and DH(t,x) ∘L J = A(t,x).
3. Define the C^∞ (k+1)-form Θ on Z by Θ(z) := ω(H z) ∘ DH(z); it is smooth by the argument of step 1. Mathlib's extDeriv_pullback applies, since ω is differentiable, H is C^∞ and minSmoothness ℝ 2 ≤ ∞. It gives dΘ(z) = dω(H z) ∘ DH(z) for all z.
4. (Cartan formula for the constant field e.) Let Θ be a (k+1)-form on Z, differentiable at z. Then d(ι_eΘ)(z) + (dΘ(z)).curryLeft e = DΘ(z)[e], where ι_eΘ := (z' ↦ Θ(z').curryLeft e). Proof: curryLeft is a continuous linear map in the covector (curryLeftLI). So ι_eΘ is differentiable at z with D(ι_eΘ)(z)[u] = (DΘ(z)[u]).curryLeft e. Evaluate at w = (w_0, …, w_k) ∈ Z^{k+1}. By extDeriv_apply, d(ι_eΘ)(z)(w) = Σ_{i=0}^k (−1)^i DΘ(z)[w_i](e, w_0, …, ŵ_i, …, w_k). Also dΘ(z)(e, w_0, …, w_k) = DΘ(z)[e](w_0, …, w_k) + Σ_{i=0}^k (−1)^{i+1} DΘ(z)[w_i](e, w_0, …, ŵ_i, …, w_k), because the (k+2)-tuple (e, w) satisfies removeNth 0 = w and removeNth (i+1) = (e, w without w_i). Adding the two expressions, the sums cancel.
5. (Pull back along j_t.) For fixed t put β_t(x) := Θ(t,x) ∘ J, α_t(x) := (ι_eΘ)(t,x) ∘ J and α^d_t(x) := ((dΘ)(t,x)).curryLeft e ∘ J. Use (γ ∘ L).curryLeft u = (γ.curryLeft (L u)) ∘ L (ContinuousAlternatingMap.curryLeft_compContinuousLinearMap), (γ ∘ L) ∘ L' = γ ∘ (L ∘L L') and step 2. This gives:
   β_t(x) = ω(h(t,x)) ∘ A(t,x). In particular β_1 = G^#ω and β_0 = F^#ω, since A(1,x) = DG(x), A(0,x) = DF(x), h(1,x) = G x and h(0,x) = F x.
   α_t(x) = (ω(h(t,x)).curryLeft V(x)) ∘ A(t,x) =: κ(t,x), the integrand of Kω.
   α^d_t(x) = (dω(h(t,x)).curryLeft V(x)) ∘ A(t,x) =: κ^d(t,x), the integrand of K(dω), using step 3.
6. ι_eΘ is C^∞ and j_t is affine, so extDeriv_pullback gives dα_t(x) = d(ι_eΘ)(t,x) ∘ J. By the chain rule, t ↦ Θ(t,x) ∘ J has derivative DΘ(t,x)[e] ∘ J, because γ ↦ γ ∘ J is continuous linear. Compose the identity of step 4 at z = (t,x) with J. For all t and x this gives
   ∂_t β_t(x) = dα_t(x) + κ^d(t,x).   (∗)
7. (Smoothness of K.) Lemma: let Y be a Banach space and f : ℝ × ℝ^P → Y C^∞. Then x ↦ ∫_0^1 f(t,x) dt is C^∞, with derivative ∫_0^1 D_x f(t,x) dt, where D_x f(t,x) := Df(t,x) ∘L J. Proof by induction on n ∈ ℕ of the claim: for every Banach space Y (all at once) and every C^∞ f, x ↦ ∫_0^1 f(t,x) dt is C^n. Write ∫_0^1 as the integral over Ioc 0 1 for the finite measure volume.restrict (Ioc 0 1) (intervalIntegral.integral_of_le).
   n = 0: fix x₀; f is bounded on the compact set [0,1] × closedBall(x₀, 1), and dominated convergence gives continuity (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous).
   n → n+1: apply hasFDerivAt_integral_of_dominated_of_fderiv_le at x₀ with neighbourhood ball(x₀, 1) and F'(x, t) := D_x f(t,x). The bound sup{‖D_x f(t,x)‖ : t ∈ [0,1], ‖x − x₀‖ ≤ 1} < ∞ holds by continuity on a compact set. This gives HasFDerivAt (x ↦ ∫ f(t,x) dt) (∫ D_x f(t,x₀) dt) x₀. The map (t,x) ↦ D_x f(t,x) is C^∞ with values in L(ℝ^P, Y), so by the induction hypothesis its integral is C^n. Then contDiff_succ_iff_hasFDerivAt gives C^{n+1}. Hence C^∞ (ContDiff ℝ ⊤ from all n).
   The integrand κ of Kω is C^∞ on ℝ × ℝ^P: (t,x) ↦ ω(h(t,x)) is C^∞; V and A are C^∞ because F, G, DF and DG are; (γ, u) ↦ γ.curryLeft u is a continuous bilinear map; and (γ, L) ↦ γ ∘ L is C^∞ as in step 1. Hence Kω is C^∞, which is the first conclusion of (b). Likewise κ^d is C^∞, since dω is.
8. (Integrate (∗).) Fix x. t ↦ β_t(x) is C^∞, and its derivative ∂_tβ_t(x) is continuous in t. The fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt) gives G^#ω(x) − F^#ω(x) = β_1(x) − β_0(x) = ∫_0^1 ∂_tβ_t(x) dt = ∫_0^1 dα_t(x) dt + ∫_0^1 κ^d(t,x) dt. Both integrands are continuous (intervalIntegral.integral_add). The last integral is K(dω)(x) by definition.
9. ∫_0^1 dα_t(x) dt = d(Kω)(x). By step 7, D(Kω)(x) = ∫_0^1 D_xκ(t,x) dt. extDeriv γ x = alternatizeUncurryFin (Dγ(x)), and alternatizeUncurryFin is a continuous linear map (alternatizeUncurryFinCLM), so it commutes with the integral (ContinuousLinearMap.integral_comp_comm or intervalIntegral_comp_comm). Since α_t = κ(t, ·), dα_t(x) = alternatizeUncurryFin(D_xκ(t,x)). Hence d(Kω)(x) = ∫_0^1 dα_t(x) dt, and step 8 gives G^#ω(x) − F^#ω(x) = d(Kω)(x) + K(dω)(x). ∎

## Key steps

1. (a) Φ^#α = compContinuousLinearMapCLM(DΦ)(α∘Φ) with compContinuousLinearMapCLM analytic, so ContDiff.clm_apply gives smoothness.
2. Write the affine homotopy as H(t,x) = F(x) + t(G(x) − F(x)) on Z = ℝ × ℝ^P and Θ := H^#ω; extDeriv_pullback gives dΘ = H^#(dω).
3. Cartan formula for the constant field e = (1,0): d(ι_eΘ) + ι_e dΘ = DΘ[e], by expanding extDeriv_apply.
4. Pull back along j_t(x) = (t,x) (extDeriv_pullback again) to get ∂_t(h_t^#ω) = d(κ(t,·)) + κ^d(t,·), where κ, κ^d are the K-integrands.
5. Smoothness of x ↦ ∫_0^1 f(t,x) dt by induction with hasFDerivAt_integral_of_dominated_of_fderiv_le; then K ω is C^∞.
6. Integrate in t (FTC) and commute d with ∫dt (alternatizeUncurryFin is a CLM) to get G^#ω − F^#ω = d(Kω) + K(dω).

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
