# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.median_deviation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3. Its first line is ∫_Q|v − v̄| ≤ Lⁿ(Q)⁻¹∫_Q∫_Q|v(x) − v(y)|. Its 'Consequently' paragraph replaces the mean v̄ by a θ-median β' with factor 1 + θ⁻¹ (Simon Ch. 2, Lemma 2.7, condition (∗)). Both hold for any integrable v; this child is the combination of the two. Notation: |W| := volume(W).toReal ∈ [0, ∞), and all integrals are over subsets of W.

0. Degenerate case. If |W| = 0, then volume(W) = 0 (it is finite), so the restricted measure volume⌞W is zero and every integral over W vanishes. Both sides are then 0; the right side has the factor ∫_W(…) = 0. Assume |W| > 0 from now on, and put v̄ := |W|⁻¹∫_W v.

1. Integrability.
 – For each fixed x, y ↦ |v(x) − v(y)| is integrable on W: it is a.e.-strongly measurable and bounded by |v(x)| + |v(y)|, and constants are integrable on W because volume(W) < ∞.
 – The function (x, y) ↦ |v(x) − v(y)| is integrable on W × W for (volume⌞W) ⊗ (volume⌞W). It is a.e.-strongly measurable (compose v with the two projections: AEStronglyMeasurable.fst/snd) and bounded by |v(x)| + |v(y)|, which is integrable for the finite product measure.
 – Hence (Fubini, Integrable.integral_prod_left) the function x ↦ ∫_W|v(x) − v(y)| dy is integrable on W.
 – Likewise x ↦ |v(x) − v̄| and x ↦ |v(x) − β| are integrable on W.

2. Mean step (the Jensen step of parent step 3). For x ∈ W, linearity of the integral gives v(x) − v̄ = |W|⁻¹∫_W (v(x) − v(y)) dy. Hence |v(x) − v̄| ≤ |W|⁻¹∫_W|v(x) − v(y)| dy. Integrate over W and use step 1 (integral_mono):
 (∗) ∫_W|v − v̄| ≤ |W|⁻¹∫_W∫_W|v(x) − v(y)| dy dx.

3. Median replacement (parent step 3, 'Consequently'). Let ṽ be a Borel function with v = ṽ a.e. on W. The sets W ∩ {β ≤ v} and W ∩ {β ≤ ṽ} differ by a null set, so they have the same measure; the same holds for W ∩ {v ≤ β} and W ∩ {ṽ ≤ β}.
 – Case β ≥ v̄. On the measurable set E₊ := W ∩ {β ≤ ṽ} we have, a.e., |v − v̄| ≥ v − v̄ ≥ β − v̄ ≥ 0. Hence (β − v̄)·volume(E₊).toReal ≤ ∫_{E₊}|v − v̄| ≤ ∫_W|v − v̄|. Here volume(E₊).toReal = volume(W ∩ {β ≤ v}).toReal ≥ θ|W| by hypothesis, and β − v̄ ≥ 0. So (β − v̄)θ|W| ≤ ∫_W|v − v̄|, i.e. |β − v̄|·|W| ≤ θ⁻¹∫_W|v − v̄|.
 – Case β < v̄. Use E₋ := W ∩ {ṽ ≤ β}: there |v − v̄| ≥ v̄ − v ≥ v̄ − β > 0 a.e. With the second hypothesis this gives the same inequality |β − v̄|·|W| ≤ θ⁻¹∫_W|v − v̄|.

4. Conclusion. Pointwise |v − β| ≤ |v − v̄| + |v̄ − β|. Integrating over W:
 ∫_W|v − β| ≤ ∫_W|v − v̄| + |v̄ − β|·|W|
  ≤ (1 + θ⁻¹)∫_W|v − v̄| (step 3)
  ≤ (1 + θ⁻¹)·|W|⁻¹·∫_W∫_W|v(x) − v(y)| dy dx (step 2, (∗)). ∎

## Key steps

1. If volume(W) = 0 both sides vanish; otherwise put v̄ := |W|⁻¹∫_W v and check integrability of all integrands (Fubini for the partial integral).
2. Jensen step: |v(x) − v̄| ≤ |W|⁻¹∫_W|v(x) − v(y)|dy, integrated over W.
3. θ-median step: on {β ≤ v} (if β ≥ v̄) or {v ≤ β} (if β < v̄) one has |v − v̄| ≥ |β − v̄|, so |β − v̄||W| ≤ θ⁻¹∫_W|v − v̄|.
4. Triangle inequality: ∫_W|v − β| ≤ (1 + θ⁻¹)∫_W|v − v̄| ≤ (1 + θ⁻¹)|W|⁻¹∫∫|v(x) − v(y)|.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean and Submission.lean (identical)`
- `cat nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-24998c59c0/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `sed -n 470,670p book/chapter-02.txt (Simon 2.1-2.7: BV definition, Lemma 2.5 mollification, Lemma 2.7 Poincare and its printed proof)`
- `python3 -I scans of dag.json: nodes matching oincar|median|mollif|BV; the cube_bv_median branch (cmcdt_cbm_* all decomposing, so not reusable); accepted helpers and frozen types of codim1_rdo_dg_sp_mollifier_adjoint, rsd_mw_tfa_smooth_cutoff, dgcr_stc_exists_normalized_mollifier, codim1_rdo_dg_sp_sobolev_limit, cutoff lemmas; freshness of dor_lmb_fcd_cp_* names; node depths (selected node depth 5)`
- `grep runtime.py (_decompose max_depth, _existing_lean_name_problem, _accepted_checkpoint), leaf_verification.check_source_delta (single theorem insertion, no imports), parent_verification.check_parent_git_delta; verifier/gmt-compare.py contract_scope and child_modules (comparator scope)`
- `git show ae0277d4 / b04a0309 (accepted adjoint and cutoff declarations, byte-identical types), 4c5953a5 and bff81d31e (non-leaf parents adding Mathlib imports, incl. Mathlib.Analysis.Calculus.BumpFunction.Convolution), ebf61002 (children proof base: frozen imports only)`
- `rg in snapshot mathlib: ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:103), normed_neg/integral_normed/support_normed_eq/contDiff_normed/hasCompactSupport_normed (BumpFunction/Normed.lean), measurePreserving_arrowProdEquivProdArrow (Constructions/Pi.lean:751), volume_preserving_piFinSuccAbove (:818), measurePreserving_pi (:907), PiLp.volume_preserving_ofLp/toLp (Haar/InnerProductSpace.lean:134,139), tendsto_measure_iUnion_atTop, tendsto_setIntegral_of_monotone, lintegral_liminf_le', exists_contDiff_support_eq_eq_one_iff`
- `rg -i 'poincar[eé] inequality|median|mollif|bounded variation' in snapshot project/GMT and .lake/packages/simongmt/Poincare (only the sorry-frozen Ch02/Ch04 contract docstrings, SimonGMT Chapter02/BV.lean basics and Chapter08 mollifier convergence outside the Ch07 import closure; no proved BV Poincare)`
- `lake env lean /tmp/cp-decomp/Avail{,2,3}.lean (#check membership of ~120 declarations in the GMT.Ch07.Submission import closure)`
- `lake env lean /tmp/cp-decomp/lean/Challenge_*.lean (13 exact comparator challenges), Assembly.lean (parent from sorried children, #print axioms), Iface.lean (interface proofs), LeafCheck.lean and proofs/{Mixed2,Slice2,Grad}.lean, Snippets.lean`
- `python3 -I /tmp/cp-decomp/num/check2.py (Monte Carlo sanity check of the coordinate-step and smooth Poincare constants)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-24998c59c0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-24998c59c0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a9900b6593/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-smooth-cutoff-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/parent_verification.py`
- `/tmp/cp-decomp/lean/Assembly.lean`
- `/tmp/cp-decomp/lean/Iface.lean`
- `/tmp/cp-decomp/lean/LeafCheck.lean`
- `/tmp/cp-decomp/proofs/Mixed2.lean`
- `/tmp/cp-decomp/proofs/Slice2.lean`
- `/tmp/cp-decomp/proofs/Grad.lean`

Snapshot (project b4d606db, Mathlib 25730c7c): Ch07 Contract.lean equals the workspace Contract.lean and Submission.lean. No proved BV Poincare inequality exists anywhere. The snapshot's Ch02 Lemma 2.7 and Ch04 5.6 are sorry-frozen contracts of other chapters. SimonGMT Chapter02/BV.lean has only variation basics. SimonGMT's mollifier a.e.-convergence (Chapter08) and Mathlib's ContDiffBump.normed and ae_convolution_tendsto_right_of_locallyIntegrable are outside the import closure of GMT.Ch07.Submission. The closure does contain convolution smoothness and support lemmas, Lebesgue differentiation, Fubini/Tonelli, piFinSuccAbove, arrowProdEquivProdArrow, measurePreserving_pi, PiLp.volume_preserving_ofLp/toLp, Fatou and the smooth Urysohn lemma. Reuse: rsd_mw_tfa_smooth_cutoff and codim1_rdo_dg_sp_mollifier_adjoint are accepted with byte-identical frozen types, so they are taken as children. The analogous cmcdt_cbm_* nodes are only decomposing, so fresh dor_lmb_fcd_cp_* names are used; all ten are unused in dag.json. Lean checks: all 12 child types and the parent type elaborate as exact comparator challenges. The parent's frozen type follows from the sorried children with the extra parent import Mathlib.Analysis.Calculus.BumpFunction.Convolution (precedent: accepted depth-5 parent codim1_rdo_dg_sobolev_perimeter). Interface proofs compile. The mixed-point and slice identities have complete leaf-form proofs using only propext, Classical.choice and Quot.sound.
