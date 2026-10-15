# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.bv_poincare-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5, last paragraph: 'By step 3 on W: ∫_W|u_ε − ū_ε| ≤ n·s·V ≤ nV, … Letting ε ↓ 0: ∫_W|u − ū| ≤ nV'. Step 3 there is proved by bounding the double integral ∫_W∫_W|v(x) − v(y)| by n·s·Lⁿ(W)·∫_W|Dv|. Here the passage to the limit is made directly in that double integral, for the mollifications along a sequence, and only almost-everywhere convergence (Lebesgue's differentiation theorem, supplied as a hypothesis) is used together with Fatou's lemma. This yields the same limit inequality as the parent's L¹-convergence argument; the mean form ∫_W|u − ū| ≤ n·s·V of the parent follows from it by the Jensen step of the sibling median_deviation.
Dependencies: sibling smooth_poincare (Submission.dor_lmb_fcd_cp_smooth_poincare) and sibling mollified_variation (Submission.dor_lmb_fcd_cp_mollified_variation).
Notation: E := Euclid (m + 1), Q := Q_δ, μ := volume⌞Q, ũ := 1_{Q₁}u, v_k := convolution (η_k) ũ (lsmul ℝ ℝ) volume, C := (m + 1)(1 − 2δ)·volume(Q).toReal ≥ 0 (as δ < 1/2).

1. Mollified functions. For each k, the sibling mollified_variation (hypotheses: u integrable on Q₁, (H), δ > 0, and the stated properties of η_k) gives: v_k is C^∞ and ∫_Q‖Dv_k‖ ≤ V.

2. Smooth Poincaré for v_k. v_k is C^∞, hence C¹, and 0 ≤ δ < 1/2. So the sibling smooth_poincare gives
 D_k := ∫_Q∫_Q|v_k(x) − v_k(y)| dy dx ≤ C·∫_Q‖Dv_k‖ ≤ C·V,
 using C ≥ 0 and step 1.

3. Almost-everywhere convergence on Q × Q.
 – Since δ > 0, Q ⊆ Q₁, so ũ = u on Q.
 – Let N be the Lebesgue-null set of x where v_k(x) → ũ(x) fails. For x ∈ Q ∖ N, v_k(x) → u(x).
 – For (x, y) ∈ (Q ∖ N) × (Q ∖ N), f_k(x, y) := |v_k(x) − v_k(y)| → f(x, y) := |u(x) − u(y)|.
 – The remaining pairs in Q × Q lie in (N × E) ∪ (E × N), which is null for μ ⊗ μ (the projections are quasi-measure-preserving). So f_k → f (μ ⊗ μ)-a.e.

4. Fatou. Each f_k is continuous, hence measurable. By Fatou's lemma (lintegral_liminf_le') for the [0, ∞]-valued integrals with respect to μ ⊗ μ, using f = liminf_k f_k a.e. (step 3):
 ∫⁻ ofReal(f) d(μ ⊗ μ) ≤ liminf_k ∫⁻ ofReal(f_k) d(μ ⊗ μ).

5. Identification with the iterated integrals.
 – Q is bounded, so μ is finite and Q̄ is compact.
 – f_k is continuous on the compact set Q̄ × Q̄, hence bounded and integrable for μ ⊗ μ. So ∫⁻ ofReal(f_k) = ofReal(∫ f_k d(μ ⊗ μ)) = ofReal(D_k) (ofReal_integral_eq_lintegral_ofReal and Fubini, integral_prod). By step 2 this is ≤ ofReal(C·V).
 – f(x, y) ≤ |u(x)| + |u(y)|. u is integrable on Q ⊆ Q₁ and μ is finite, so f is integrable for μ ⊗ μ; its a.e.-strong measurability comes from AEStronglyMeasurable.fst/snd.
 – Hence ∫_Q∫_Q|u(x) − u(y)| dy dx = ∫ f d(μ ⊗ μ) (integral_prod) = (∫⁻ ofReal(f) d(μ ⊗ μ)).toReal ≤ (ofReal(C·V)).toReal = C·V. The last equality uses C·V ≥ 0: V ≥ ∫_Q‖Dv_0‖ ≥ 0 by step 1.

Therefore ∫_Q∫_Q|u(x) − u(y)| dy dx ≤ (m + 1)·(1 − 2δ)·volume(Q_δ).toReal·V. ∎

## Key steps

1. Sibling mollified_variation: v_k = η_k∗(1_{Q₁}u) is C^∞ with ∫_{Q_δ}‖Dv_k‖ ≤ V.
2. Sibling smooth_poincare: ∫∫_{Q_δ×Q_δ}|v_k(x) − v_k(y)| ≤ (m + 1)(1 − 2δ)volume(Q_δ)·V.
3. a.e. convergence v_k → u on Q_δ ⊆ Q₁ gives |v_k(x) − v_k(y)| → |u(x) − u(y)| for a.e. (x, y) ∈ Q_δ × Q_δ.
4. Fatou on the finite product measure plus Fubini identifications pass the bound to u.

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
