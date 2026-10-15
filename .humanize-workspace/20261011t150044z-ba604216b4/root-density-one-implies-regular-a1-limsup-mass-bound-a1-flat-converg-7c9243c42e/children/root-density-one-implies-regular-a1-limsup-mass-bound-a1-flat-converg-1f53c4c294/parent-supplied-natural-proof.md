# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.homotopy_maps-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4: the cut-off homotopy Ĥ is Lipschitz, Ĥ_j are C¹ and Lipschitz with a constant independent of j, Ĥ_j → Ĥ' uniformly, and for t ∈ (0,1) and x near E (where χ̃ ≡ 1 and s(t) = t) the form (Ĥ_j^#ω)₁(t,x) is the integrand of K_jω. Self-contained; no siblings.
Notation: pr, y₀, ι, ê₀ as in the statement; J v := ι(0,v). pr(ι(t,x)) = x and (ι(t,x))₀ = t by rfl. pr and y ↦ y₀ are continuous linear with norm ≤ 1, so ‖pr y − pr y'‖ ≤ ‖y − y'‖ and |y₀ − y'₀| ≤ ‖y − y'‖. Let K := tsupport χ (compact) and B_χ := sup|χ| < ∞ (χ is continuous with compact support).
Part (A).
1. Let D := sup_K ‖G − F‖ (0 if K = ∅; finite by continuity on a compact set) and φ := χ·(G − F). Then ‖φ‖ ≤ B_χ·D everywhere, since φ = 0 off K.
2. φ is (L_χD + 2ΛB_χ)-Lipschitz. Let x, x' ∈ ℝ^P. If neither lies in K, φ(x) = φ(x') = 0. Otherwise, by symmetry, x' ∈ K. Write φ(x) − φ(x') = (χ(x) − χ(x'))·(G − F)(x') + χ(x)·((G − F)(x) − (G − F)(x')). The first term has norm ≤ L_χ‖x − x'‖·D. The second term is 0 if χ(x) = 0, and otherwise has norm ≤ B_χ·2Λ‖x − x'‖.
3. H_{F,G}(y) = F(pr y) + a(y₀)•φ(pr y). Hence ‖H_{F,G}(y) − H_{F,G}(y')‖ ≤ Λ‖y − y'‖ + |a(y₀) − a(y'₀)|·‖φ(pr y)‖ + |a(y'₀)|·‖φ(pr y) − φ(pr y')‖ ≤ (Λ + L_aB_χD + A(L_χD + 2ΛB_χ))‖y − y'‖. Conclude with LipschitzWith.of_dist_le_mul.
Part (B). Put H_j := H_{F_j,G_j} and V_j := G_j − F_j.
4. H_j is C¹: pr and y ↦ y₀ are continuous linear, and sums, products, scalar multiplications and compositions of C¹ maps are C¹ (ContDiff.add, ContDiff.smul, ContDiff.mul, ContDiff.comp).
5. Bounds. a is C¹ and L_a-Lipschitz, so |a'| ≤ L_a (norm_deriv_le_of_lipschitz or norm_fderiv_le_of_lipschitz). χ is C¹ and L_χ-Lipschitz, so ‖Dχ‖ ≤ L_χ; also Dχ = 0 off K (fderiv vanishes off tsupport). F_j, G_j are Λ-Lipschitz, so ‖DF_j‖, ‖DG_j‖ ≤ Λ. Put D₂ := sup_j sup_K ‖V_j‖, which is finite: by uniform convergence ‖V_j − (G − F)‖_∞ ≤ 2 for j ≥ j₀, so ‖V_j‖ ≤ D + 2 on K for j ≥ j₀; each of the finitely many V_j with j < j₀ is continuous, hence bounded on the compact K.
6. By the product and chain rules, DH_j(y) = DF_j(pr y)∘pr + (a'(y₀)χ(pr y))·(c ↦ c₀)⊗V_j(pr y) + a(y₀)·(Dχ(pr y)∘pr)⊗V_j(pr y) + a(y₀)χ(pr y)·(DG_j(pr y) − DF_j(pr y))∘pr. When pr y ∉ K the last three terms vanish. Hence ‖DH_j(y)‖ ≤ Λ + L_aB_χD₂ + AL_χD₂ + 2AB_χΛ =: L for all j and y. By the mean value inequality on the convex space (lipschitzWith_of_nnnorm_fderiv_le), every H_j is L-Lipschitz.
7. For all y, ‖H_j(y) − H_{F,G}(y)‖ ≤ ‖F_j(pr y) − F(pr y)‖ + A·B_χ·(‖G_j(pr y) − G(pr y)‖ + ‖F_j(pr y) − F(pr y)‖) ≤ (1 + AB_χ)·sup‖F_j − F‖ + AB_χ·sup‖G_j − G‖ → 0. Hence H_j → H_{F,G} uniformly (Metric.tendstoUniformly_iff).
Part (C). Put z := ι(t,x).
8. The set O := {y : pr y ∈ W, y₀ ∈ (−1, 2)} is open and contains z. On O we have χ(pr y) = 1 and a(y₀) = y₀, so H'(y) = F'(pr y) + y₀•(G'(pr y) − F'(pr y)) =: H''(y). Thus H' =ᶠ[𝓝 z] H'', so H'(z) = H''(z) and DH'(z) = DH''(z) (Filter.EventuallyEq.fderiv_eq).
9. H'' is differentiable at z with DH''(z)(c) = DF'(x)(pr c) + c₀·(G'x − F'x) + t·(DG'(x) − DF'(x))(pr c). Hence H'(z) = F'x + t(G'x − F'x). Moreover DH'(z)ê₀ = G'x − F'x, because pr ê₀ = 0 and ê₀₀ = 1. And DH'(z) ∘L J = DF'(x) + t(DG'(x) − DF'(x)), because pr(Jv) = v and (Jv)₀ = 0.
10. x' ↦ ι(t,x') equals ι(t,0) + Jx', so fderiv ℝ (x' ↦ ι(t,x')) x = J.
11. Use ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, (g.compContinuousLinearMap f).curryLeft v = (g.curryLeft (f v)).compContinuousLinearMap f, and (γ ∘ L) ∘ L' = γ ∘ (L ∘L L') (ext). They give ((ω(H'z) ∘ DH'(z)).curryLeft ê₀) ∘ J = (ω(H'z).curryLeft (DH'(z)ê₀)) ∘ (DH'(z) ∘L J). By steps 9 and 10 this equals (ω(F'x + t(G'x − F'x)).curryLeft (G'x − F'x)) ∘ (DF'(x) + t(DG'(x) − DF'(x))). ∎

## Key steps

1. (A) φ = χ(G − F) is bounded and Lipschitz (case analysis on tsupport χ), and a is bounded and Lipschitz, so H = F∘pr + a(y₀)φ(pr y) is Lipschitz.
2. (B) H_j is C¹ and ‖DH_j‖ ≤ Λ + L_aB_χD₂ + AL_χD₂ + 2AB_χΛ with D₂ = sup_j sup_K‖G_j − F_j‖ < ∞; mean value inequality; uniform convergence from that of F_j, G_j.
3. (C) Near ι(t,x), H′ = F′∘pr + y₀(G′ − F′)∘pr; so DH′ê₀ = G′x − F′x and DH′∘J = DF′ + t(DG′ − DF′); curryLeft_compContinuousLinearMap gives the integrand of K.

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
