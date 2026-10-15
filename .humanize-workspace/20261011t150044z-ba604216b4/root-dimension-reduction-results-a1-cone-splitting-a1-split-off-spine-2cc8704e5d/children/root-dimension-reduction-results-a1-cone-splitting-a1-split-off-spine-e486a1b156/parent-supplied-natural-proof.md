# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.radial_homotopy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- Λ^j := Covector (Euclid P) j, the continuous alternating j-linear forms on ℝ^P with the operator norm. It is finite-dimensional, hence complete.
- ι_xα := α.curryLeft x, so (ι_xα)(v_1, …, v_j) = α(x, v_1, …, v_j).
- d = exteriorDerivative = Mathlib extDeriv: dω(x) = alt(Dω(x)), where alt := ContinuousAlternatingMap.alternatizeUncurryFin is a continuous linear map (alternatizeUncurryFinCLM) and D := fderiv ℝ.
- h(t, x) := t^q • ι_x(β(t•x)) for (t, x) ∈ ℝ × ℝ^P. So Kβ(x) = ∫_0^1 h(t, x) dt.
- K′(dβ)(x) := ∫_0^1 t^{q+1} • ι_x((dβ)(t•x)) dt.

1. h is C^∞.
 - (t, x) ↦ t^q and (t, x) ↦ t•x are C^∞, so (t, x) ↦ β(t•x) is C^∞ (composition with the C^∞ map β).
 - Φ : Λ^{q+1} × ℝ^P → Λ^q, Φ(f, z) := f.curryLeft z, is continuous and bilinear: f ↦ f.curryLeft is the linear isometry ContinuousAlternatingMap.curryLeftLI : Λ^{q+1} → L(ℝ^P, Λ^q), followed by evaluation, which is bounded bilinear. Hence Φ is C^∞.
 - Scalar multiplication ℝ × Λ^q → Λ^q is C^∞.
 So h(t, x) = t^q • Φ(β(t•x), x) is C^∞ on ℝ × ℝ^P.
2. Smoothness and derivative of Kβ. Apply the sibling param_integral (the accepted cmcdt_lpo_slice_param_integral) with N := P, V := Λ^q (a complete real normed space) and h.
 - x ↦ ∫_0^1 h(t, x) dt = Kβ is C^∞. This is conclusion (1).
 - For every x, Kβ has Fréchet derivative D(Kβ)(x) = ∫_0^1 D_x h(t, ·)(x) dt, where D_x h(t, ·)(x) := fderiv ℝ (x′ ↦ h(t, x′)) x = Dh(t, x) ∘L inr.
3. Exterior derivative of Kβ.
 - t ↦ D_x h(t, ·)(x) = Dh(t, x) ∘L inr is continuous, because h is C^1 and so Dh is continuous. Hence it is interval integrable on [0, 1].
 - alt is a continuous linear map, so it commutes with the interval integral (ContinuousLinearMap.intervalIntegral_comp_comm):
 d(Kβ)(x) = alt(∫_0^1 D_x h(t, ·)(x) dt) = ∫_0^1 alt(D_x h(t, ·)(x)) dt = ∫_0^1 d(h(t, ·))(x) dt.
4. Pointwise identity. Fix t ∈ ℝ and x ∈ ℝ^P. Let β_t(y) := β(t•y), which is C^∞, and ψ_t(y) := ι_y(β_t(y)) = (β_t(y)).curryLeft y. Then h(t, ·) = t^q • ψ_t.
 (a) Chain rule. β_t = β ∘ (t • id), so Dβ_t(x) = Dβ(t•x) ∘L (t • id) = t • Dβ(t•x). Applying alt gives dβ_t(x) = t • (dβ)(t•x). Evaluating at x gives Dβ_t(x)[x] = t • Dβ(t•x)[x].
 (b) Cartan's formula. Apply the sibling euler_cartan (the accepted dtc_cone_euler_cartan) with m := q, β := β_t, y := x; β_t is differentiable at x:
 dψ_t(x) + ι_x(dβ_t(x)) = ((q : ℝ) + 1) • β_t(x) + Dβ_t(x)[x].
 (c) d commutes with constant scalars (exteriorDerivative_smul), so d(h(t, ·))(x) = t^q • dψ_t(x). Multiply (b) by t^q and use (a) and curryLeft_smul (ι_x(t•α) = t•ι_xα):
 d(h(t, ·))(x) + t^{q+1} • ι_x((dβ)(t•x)) = ((q : ℝ) + 1)·t^q • β(t•x) + t^{q+1} • Dβ(t•x)[x].   (∗)
 (d) The right side of (∗) is g′(t), where g(t) := t^{q+1} • β(t•x) : ℝ → Λ^{q+1}. Indeed, by the product rule and the chain rule (the derivative of t ↦ t•x is x), HasDerivAt g (((q : ℝ) + 1)·t^q • β(t•x) + t^{q+1} • Dβ(t•x)[x]) t.
 Remark. Expanding both sides of (∗) with exteriorDerivative_apply gives exactly the computation in step 2 of the parent proof. The terms Σ_i (−1)^{i−1} Dβ(tx)[v_i](x, v_1, …, v̂_i, …, v_q) of d(h(t,·))(x)(v) cancel against the terms Σ_i (−1)^i Dβ(tx)[v_i](x, …) of ι_x(dβ)(tx)(v). Cartan's formula packages this cancellation.
5. Integration.
 - All terms of (∗) are continuous in t: β, Dβ and dβ = alt ∘ Dβ are continuous, and t ↦ d(h(t, ·))(x) is continuous as in step 3. So all are interval integrable on [0, 1].
 - Integrate (∗) over [0, 1] and apply the fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt with step 4(d)):
 ∫_0^1 d(h(t, ·))(x) dt + ∫_0^1 t^{q+1} • ι_x((dβ)(t•x)) dt = g(1) − g(0) = β(x) − 0^{q+1} • β(0) = β(x),
 since q + 1 ≥ 1.
6. By steps 3 and 5, d(Kβ)(x) + K′(dβ)(x) = β(x) for every x ∈ ℝ^P. This is conclusion (2). ∎

Checks made during decomposition. The formula with exactly these exponents (t^q in K, t^{q+1} in K′) and Mathlib's sign conventions for extDeriv and curryLeft was verified numerically for random polynomial forms with (P, q) ∈ {(2,0), (3,0), (3,1), (3,2), (4,1), (4,2)} (errors ≤ 1e−10). Its use in the sibling cone_current (the boundary step) was compiled in Lean.

## Key steps

1. h(t,x) := t^q ι_x β(tx) is C^∞ on ℝ × ℝ^P. By the accepted parametric-integral lemma (sibling param_integral), Kβ = ∫_0^1 h(t,·) dt is C^∞, with D(Kβ)(x) = ∫_0^1 D_x h(t,·)(x) dt.
2. alt = alternatizeUncurryFin is a continuous linear map, so d(Kβ)(x) = ∫_0^1 d(h(t,·))(x) dt.
3. Cartan's formula (sibling euler_cartan) for β_t = β(t·), with dβ_t(x) = t dβ(tx) and Dβ_t(x)x = t Dβ(tx)x, gives d(h(t,·))(x) + t^{q+1} ι_x dβ(tx) = (q+1) t^q β(tx) + t^{q+1} Dβ(tx)[x] = (d/dt)(t^{q+1} β(tx)).
4. Integrating over [0,1] (FTC; 0^{q+1} = 0) gives d(Kβ)(x) + ∫_0^1 t^{q+1} ι_x dβ(tx) dt = β(x).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606d, 25730c7c, 2b36630: pins match)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 over dag.json: siblings of split_off_spine-a1; regex search of statements and lean_statements for homotop|cone|parametriz|push-?forward|curryLeft|Matrix.det with covectorEuclideanNorm; statuses and candidate commits of the reuse candidates`
- `python3 over dag.json: the subtrees …moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_pushforward-a1 (lpip_*) and …flat_convergence-a1.deformation-a1.im_pushforward-a1 (dor_lmb_fcd_imp_*); parallel node idtp_fons_cs_sos_cone_filling_in_subspace (same type, rlcr-lean, not accepted); dor_lmb_fcd_imp_parametric_rep (comparing, not accepted); dor_lmb_fc_im_series (decomposing, not accepted)`
- `git show <candidate commit>:GMT/Ch07/Submission.lean | grep import, for 551eaab, 3d04d72, 918eb38, 9b823b5, 44ef61f, 27de75e, 2af75d6, a2ba78f, 2fd8f6f, 0ea228e, 77ba671 (the lpip commits add import Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `grep SimonGMT Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean for TestFormOnConverges, GeometricCurrentOn, boundary_apply, zeroRegion, support, massOn, massAdmissibleOn, covectorEuclideanNorm, IsSmoothForm, exteriorDerivative`
- `grep the Mathlib snapshot for ParametricIntegral and ParametricIntervalIntegral (no ContDiff lemma for parametric integrals, so the accepted cmcdt_lpo_slice_param_integral is reused), Alternating/Curry.lean (norm_curryLeft, curryLeftLI), BumpFunction/Basic.lean, Constructions/Pi.lean (volume_preserving_piFinSuccAbove), Haar/InnerProductSpace.lean (PiLp.volume_preserving_ofLp/toLp), ContDiff/RCLike.lean (ContDiff.lipschitzWith_of_hasCompactSupport)`
- `lake env lean /tmp/cfs-decomp/Check1.lean, Check2.lean, Check3.lean, Check4.lean after import GMT.Ch07.Submission with the contract opens`
- `python3 -I /tmp/cfs-scripts/homotopy_num.py (numeric check of the radial homotopy formula with Mathlib extDeriv/curryLeft conventions)`
- `grep -c dimred_cs_sos_cfs dag.json (0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-14afd577b6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-equals-rep-measure-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/tmp/cfs-decomp/Check1.lean`
- `/tmp/cfs-decomp/Check2.lean`
- `/tmp/cfs-decomp/Check3.lean`
- `/tmp/cfs-decomp/Check4.lean`

Pins and contract. The pins match: project b4d606d, mathlib 25730c7c, SimonGMT 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and the selected node's proof base 480b1bd contains only the contract.

Library gaps. Mathlib has no lemma for smoothness of parametric integrals; this is covered by the accepted cmcdt_lpo_slice_param_integral. SimonGMT has no cone, homotopy or Lipschitz-pushforward constructions. Every other API cited by the child proofs exists and was probed with #check, including:
- norm_curryLeft, curryLeftLI, alternatizeUncurryFinCLM, ContinuousAlternatingMap.apply;
- ContDiffBump, ContDiff.lipschitzWith_of_hasCompactSupport, Filter.EventuallyEq.fderiv_eq;
- intervalIntegral_comp_comm, integral_eq_sub_of_hasDerivAt, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp;
- measurable_fderiv, norm_fderiv_le_of_lipschitz, enorm_integral_le_lintegral_enorm, HasSum.unique.

Reuse. Comparator-accepted DAG declarations with byte-identical frozen types are reused:
- 6 as siblings: cmcdt_lpo_slice_param_integral, dtc_cone_euler_cartan, cmcdt_lp_covector_curryLeft_norm_le, dtc_vanish_off_support, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub;
- 6 cited for the depth-6 wiring of two children: dimred_mbl_dt_lpip_normalized_rep, dimred_mbl_dt_lpip_piece_representation, dpf_rectifiable_bilipschitz_pieces, covectorEuclideanNorm_gram_bounds, dimred_mbl_dt_lpip_lipschitz_piece_current, cmcdt_im_series.
The three lpip commits add import Poincare.SimonGMT.Chapter02.AreaLipschitz, which is inherited through the merge. The other commits add no imports.

Not reused (not accepted): the parallel same-type node idtp_fons_cs_sos_cone_filling_in_subspace (rlcr-lean), dor_lmb_fcd_imp_parametric_rep (comparing), dor_lmb_fc_im_series and emf_exists_cone_filling (decomposing).

Lean checks:
- Check1: all child types (and the 6 wiring types) elaborate as Submission stubs, and the frozen parent type is proved from the 5 new child types. Axioms: propext, sorryAx (stubs only), Classical.choice, Quot.sound.
- Check2: compact_im_param and param_series_im are fully proved from the frozen types of the accepted lemmas they cite.
- Check3: the homotopy formula aligns by rfl with cone_current's boundary step, Kω is smooth for test forms, and the ContDiffBump cutoff works.
- Check4: covector evaluation commutes with interval integrals.
- The radial homotopy formula was also checked numerically.

Names: the 5 new dimred_cs_sos_cfs_* names occur nowhere in dag.json.
