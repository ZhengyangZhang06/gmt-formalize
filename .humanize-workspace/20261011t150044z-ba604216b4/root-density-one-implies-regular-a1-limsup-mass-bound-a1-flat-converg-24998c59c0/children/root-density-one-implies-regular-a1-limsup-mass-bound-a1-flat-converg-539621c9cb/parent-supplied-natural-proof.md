# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.shrinking-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 4 (as in Simon's printed proof of Ch. 2, 2.7: 'choose convex W ⊂⊂ U such that ∫_U|u − β| ≤ 2∫_W|u − β| … for example W = {x ∈ U : dist(x, ∂U) > δ}'). We must choose δ ∈ (0, 1/4] with Lⁿ(Q₁ ∖ Q_δ) ≤ 1/4 and ∫_{Q₁∖Q_δ}|f| ≤ ½∫_{Q₁}|f|, using continuity of measure and of the integral. With Q_δ ⊆ Q₁ the latter is equivalent to ∫_{Q₁}|f| ≤ 2∫_{Q_δ}|f|. In the parent this is applied to f = u − β. Notation: L := volume on Euclid (m + 1).

1. Basic facts.
 – Q₁ and every Q_δ are open (finite intersections of open coordinate half-spaces), hence measurable.
 – L(Q₁) = 1: the coordinate map WithLp.ofLp is measure preserving (PiLp.volume_preserving_ofLp) and maps Q₁ onto the box ∏(0, 1), of measure 1 (Real.volume_pi_Ioo).
 – For δ ≥ 0, Q_δ ⊆ Q₁, hence L(Q_δ) ≤ 1.

2. Exhaustion. Put δ_j := 1/(j + 4) for j ∈ ℕ, so 0 < δ_j ≤ 1/4 and δ_j decreases to 0.
 – The sets Q_{δ_j} increase with j.
 – ⋃_j Q_{δ_j} = Q₁. If y ∈ Q₁ then r := min_i min(y_i, 1 − y_i) > 0 (finitely many coordinates), and y ∈ Q_{δ_j} as soon as δ_j < r.

3. Measure of the boundary layer. The sets Q₁ ∖ Q_{δ_j} are measurable and decreasing, have empty intersection (step 2), and have finite measure (≤ 1). By continuity from above (tendsto_measure_iInter_atTop), L(Q₁ ∖ Q_{δ_j}) → 0. Choose j₁ with L(Q₁ ∖ Q_{δ_j}) ≤ 1/4 for all j ≥ j₁ (the sequence is nonincreasing).

4. Integral. |f| is integrable on Q₁ = ⋃_j Q_{δ_j}, an increasing union of measurable sets. So ∫_{Q_{δ_j}}|f| → ∫_{Q₁}|f| (tendsto_setIntegral_of_monotone).
 – If ∫_{Q₁}|f| = 0, every δ satisfies ∫_{Q₁}|f| = 0 ≤ 2∫_{Q_δ}|f|; put j₂ := 0.
 – Otherwise ∫_{Q₁}|f| > ½∫_{Q₁}|f|, so there is j₂ with ∫_{Q_{δ_j}}|f| ≥ ½∫_{Q₁}|f| for all j ≥ j₂ (the sequence is nondecreasing).

5. Take j := max(j₁, j₂) and δ := δ_j. Then 0 < δ ≤ 1/4, L(Q_δ) ≤ 1 (step 1), L(Q₁ ∖ Q_δ) ≤ 1/4 (step 3) and ∫_{Q₁}|f| ≤ 2∫_{Q_δ}|f| (step 4). ∎

## Key steps

1. Q₁ and Q_δ are open; volume(Q₁) = 1 and Q_δ ⊆ Q₁.
2. Q_{1/(j+4)} increases to Q₁.
3. Continuity from above: volume(Q₁ ∖ Q_{1/(j+4)}) → 0.
4. Continuity of the integral: ∫_{Q_{1/(j+4)}}|f| → ∫_{Q₁}|f|; pick j large for both.

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
