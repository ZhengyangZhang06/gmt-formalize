# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.pointwise-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 4 (pointwise bound (4.9) of Simon Ch. 6 for the slice ⟨T, f, t₋⟩ of 4.6), steps (4e)–(4f): let the cut-offs χ_{h,ε} tend to the indicator of {f < t} (h ↓ 0), then ε ↓ 0, then take the supremum over admissible ω. The fixed-cut-off estimate (4a)–(4d) is the sibling `slicing_mb_cutoff_defect_bound`, and the cut-offs are those of the sibling `slicing_mb_cutoff`.

Setting. P, m ∈ ℕ; U ⊆ ℝ^P open; T ∈ D_{m+1}(U); (μ, v) with IsMeasureRepresentation T μ v, μ(K′) < ∞ for every compact K′ ⊆ U, and |v(x)(α)| ≤ |α| for all x, α (|·| = covectorEuclideanNorm); f : ℝ^P → ℝ L-Lipschitz on U; t ∈ ℝ; S ∈ D_m(U) with IsSlice T f t S; W ⊆ U open; LW ≥ 0 with ‖Df(x)‖ ≤ LW for Lebesgue-a.e. x ∈ W. Put A_t := {x | x ∈ U ∧ f(x) < t} and
 Λ(t) := liminf_{h → 0+} μ(W ∩ f⁻¹([t − h, t])) / h ∈ [0,∞]
(the liminf along the filter 𝓝[>] 0, quotients in [0,∞]). Claim: M_W(S) ≤ LW·Λ(t), with products in [0,∞] (0·∞ = 0).

1. (Unpacking the slice.) IsSlice T f t S gives currents A ∈ D_{m+1}(U), B ∈ D_m(U) with IsRestriction T A_t A, IsRestriction ∂T A_t B, and S(ω) = ∂A(ω) − B(ω) = A(dω) − B(ω) for every ω ∈ D^m(U) (dω := exteriorDerivative ω, viewed as the test form exteriorDerivativeTestOn U m ω ∈ D^{m+1}(U)). IsRestriction T A_t A provides: A_t is Borel, and (μ₁, v₁) with IsMeasureRepresentation T μ₁ v₁ and A(η) = ∫_{A_t} v₁(x)(η(x)) dμ₁ for all η ∈ D^{m+1}(U). IsRestriction ∂T A_t B provides (μ₂, v₂) with IsMeasureRepresentation ∂T μ₂ v₂ and B(ω) = ∫_{A_t} v₂(x)(ω(x)) dμ₂ for all ω ∈ D^m(U). Hence, for every ω ∈ D^m(U),
 S(ω) = ∫_{A_t} v₁(x)(dω(x)) dμ₁ − ∫_{A_t} v₂(x)(ω(x)) dμ₂.

2. (Reduction to admissible ω.) M_W(S) = S.massOn W is the supremum of ofReal(S(ω)) over ω ∈ D^m(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. So it suffices to show ofReal(S(ω)) ≤ LW·Λ(t) for every such ω. Fix one, put K := tsupport ω (compact, K ⊆ W ⊆ U), and fix ε > 0.

3. (Fixed cut-off.) For h > 0 let χ_h be the function given by `slicing_mb_cutoff` for (t, h, ε): C^∞, 0 ≤ χ_h ≤ 1 (so |χ_h| ≤ 1), χ_h(s) = 1 for s ≤ t − h, χ_h(s) = 0 for s ≥ t, |χ_h′| ≤ (1+ε)/h, and χ_h′(s) = 0 for s ∉ (t − h, t). Put
 X(h) := ∫ χ_h(f(x))·v₂(x)(ω(x)) dμ₂ − ∫ χ_h(f(x))·v₁(x)(dω(x)) dμ₁.
By `slicing_mb_cutoff_defect_bound` (with (μ, v), (μ₁, v₁), (μ₂, v₂), f, L, W, LW, ω, χ_h, t, h and c := (1+ε)/h; its hypotheses hold by the setting, step 1 and the properties of χ_h), for every h > 0:
 ofReal|X(h)| ≤ ofReal((1+ε)/h)·LW·μ(K ∩ f⁻¹([t − h, t])).

4. (h ↓ 0: the cut-offs converge to the indicator of A_t.) Let x ∈ U. If f(x) < t, then for 0 < h ≤ t − f(x) we have f(x) ≤ t − h, so χ_h(f(x)) = 1 = 1_{A_t}(x). If f(x) ≥ t, then χ_h(f(x)) = 0 = 1_{A_t}(x) for every h. Hence χ_h(f(x)) → 1_{A_t}(x) as h → 0+, for every x ∈ U. If x ∉ U then x ∉ tsupport ω and x ∉ tsupport dω (both are contained in U), so ω(x) = 0 and dω(x) = 0 and all integrands below vanish at x. Therefore, for every x, χ_h(f(x))·v₂(x)(ω(x)) → 1_{A_t}(x)·v₂(x)(ω(x)) and χ_h(f(x))·v₁(x)(dω(x)) → 1_{A_t}(x)·v₁(x)(dω(x)) as h → 0+. The integrands are a.e.-strongly measurable (they vanish off K, and x ↦ 1_K(x)χ_h(f(x)) is Borel because f is continuous on the closed set K ⊆ U; the second factors are integrable by IsMeasureRepresentation, as ω and dω are test forms) and dominated by the integrable functions |v₂(x)(ω(x))| and |v₁(x)(dω(x))|. (Alternatively, replace f inside these integrands by a continuous McShane extension f̃ of f|U, which changes nothing because the integrands vanish off K and f̃ = f on K ⊆ U.) By dominated convergence along h → 0+ (the filter 𝓝[>] 0 is countably generated; `tendsto_integral_filter_of_dominated_convergence`),
 X(h) → ∫_{A_t} v₂(x)(ω(x)) dμ₂ − ∫_{A_t} v₁(x)(dω(x)) dμ₁ = −S(ω)  (step 1; A_t is Borel, so ∫_{A_t} F = ∫ 1_{A_t}F).
Hence ofReal|X(h)| → ofReal|S(ω)| as h → 0+.

5. (Liminf.) For h > 0, ofReal((1+ε)/h) = ofReal(1+ε)/ofReal(h), so the right side of step 3 equals C_ε·μ(K ∩ f⁻¹([t − h, t]))/ofReal(h) with C_ε := ofReal(1+ε)·LW < ∞, and this is ≤ C_ε·μ(W ∩ f⁻¹([t − h, t]))/ofReal(h) because K ⊆ W. From steps 3 and 4,
 ofReal|S(ω)| = lim_{h→0+} ofReal|X(h)| ≤ liminf_{h→0+} C_ε·μ(W ∩ f⁻¹([t − h, t]))/ofReal(h) = C_ε·Λ(t),
using that multiplication by the finite constant C_ε commutes with liminf in [0,∞] (`ENNReal.liminf_const_mul_of_ne_top`). Since ofReal(S(ω)) ≤ ofReal|S(ω)|, we get ofReal(S(ω)) ≤ ofReal(1+ε)·LW·Λ(t) for every ε > 0.

6. (ε ↓ 0.) If LW·Λ(t) = ∞ there is nothing to prove. Otherwise LW·Λ(t) < ∞ and ofReal(1+ε)·LW·Λ(t) → LW·Λ(t) as ε ↓ 0, so ofReal(S(ω)) ≤ LW·Λ(t). (If LW = 0, both sides of step 5 are computed with 0·Λ(t) = 0, and the conclusion is ofReal(S(ω)) ≤ 0.)

7. (Supremum.) Since ω was an arbitrary admissible form, M_W(S) = sup ofReal(S(ω)) ≤ LW·Λ(t), i.e.
 S.massOn W ≤ LW · liminf_{h→0+} μ(W ∩ f⁻¹([t − h, t]))/ofReal(h). ∎

## Key steps

1. Unpack IsSlice: S(ω) = ∫_{A_t} v₁(dω) dμ₁ − ∫_{A_t} v₂(ω) dμ₂ with A_t = {x ∈ U : f(x) < t}; reduce to admissible ω with K = tsupport ω ⊆ W.
2. For h > 0 take the cut-off χ_h of slicing_mb_cutoff; slicing_mb_cutoff_defect_bound gives ofReal|X(h)| ≤ ofReal((1+ε)/h)·LW·μ(K ∩ f⁻¹([t−h, t])).
3. h → 0+: χ_h(f) → 1_{A_t} on U, dominated convergence gives X(h) → −S(ω); hence ofReal|S(ω)| ≤ (1+ε)·LW·liminf_h μ(W ∩ f⁻¹([t−h, t]))/h.
4. ε ↓ 0 and supremum over admissible ω give (4.9).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `rg -n 'slicing_mb_' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem norm_deriv_le_of_lipschitz|theorem LipschitzOnWith.extend_real|theorem LipschitzWith.ae_differentiableAt|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegrable_deriv|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem liminf_const_mul_of_ne_top|theorem hasDerivAt_integral_of_dominated_loc_of_lip|HasCompactSupport.contDiff_convolution_left|theorem alternatizeUncurryFin_apply|theorem tendsto_measure_biInter_gt|theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq|theorem fderiv_fun_smul|theorem ofReal_integral_eq_lintegral_ofReal|theorem tendsto_integral_filter_of_dominated_convergence' local-references/197bdd4b88278494/mathlib/Mathlib/{Analysis,Order,MeasureTheory,Topology,LinearAlgebra}`
- `grep -n 'covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev exteriorDerivative|abbrev TestFormOn|structure GeometricCurrentOn|boundary_apply|tsupport_exteriorDerivative_subset|abbrev NVector' simongmt/Poincare/SimonGMT/Chapter06/{Mass,Forms,Currents,FormsDuality}.lean`
- `python3 scan of dag.json (200 nodes): lean_name uniqueness of the seven proposed names; search of titles/statements/lean_statements for alternatizeUncurryFin, smulRight, liminf, Monotone, cut-off, mollif, wedge, Dini, McShane, Rademacher (no identical type)`
- `python3 read of nodes/root-slicing-a1-slice-mass-bound-a1/{parent-child-handoff.json, decomposition-v3.json, decomposition-audit-v1..v4.json, decomposition-review-receipt-v1..v4.json}`
- `python3 read of .humanize/swarm-configs/*.json for github_selected_issue 676: 97b6c024c2834d99b1a86982198ed548.json max_nodes=1000 max_depth=6 (older 9bd566bbce374e36839dbfed5b2a4b01.json max_nodes=200)`
- `contract_scope/child_modules in verifier/gmt-compare.py (replayed child scope)`
- `lake env printenv LEAN_PATH; lean -o /tmp/smb_split_v5_bWB45t/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/smb_split_v5_bWB45t/check/Stmts.lean (7 child types + parent in the comparator child scope: 0 errors)`
- `lean /tmp/smb_split_v5_bWB45t/check/Instances.lean (wedge degree m+1, operator norms by rfl, C^∞ index)`
- `lean /tmp/smb_split_v5_bWB45t/check/Assembly.lean (#print axioms HumanizeNodeComparator.assembly: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/smb_split_v5_bWB45t/check/Plumbing.lean (dependency instantiations type-check)`
- `lean /tmp/smb_split_v5_bWB45t/check/Names.lean (#check of every lemma cited in the child proofs)`
- `sed -n '1340,1415p' book/chapter-06.txt (Simon Ch. 6, 4.6–4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/97b6c024c2834d99b1a86982198ed548.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/smb_split_v5_bWB45t/check/Stmts.lean`
- `/tmp/smb_split_v5_bWB45t/check/Instances.lean`
- `/tmp/smb_split_v5_bWB45t/check/Assembly.lean`
- `/tmp/smb_split_v5_bWB45t/check/Plumbing.lean`
- `/tmp/smb_split_v5_bWB45t/check/Names.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and it is byte-identical to the workspace Submission, so child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies GeometricCurrentOn with boundary ∂T(ω) = T(dω), massOn via covectorEuclideanNorm, TestFormOn, exteriorDerivative (Mathlib's extDeriv, i.e. alternatizeUncurryFin ∘ fderiv) and tsupport_exteriorDerivative_subset. Mathlib supplies McShane extension (LipschitzOnWith.extend_real), Rademacher's theorem (LipschitzWith.ae_differentiableAt), convolution smoothness, differentiation under the integral, Lebesgue's theorem for monotone functions with the integral bound for their derivative, liminf algebra in ℝ≥0∞, dominated convergence along countably generated filters and continuity from above. Every cited name exists at the pinned revision. Neither library contains the sharp cut-off, the wedge coefficient-norm bound, the smooth approximation with an a.e. gradient bound, the slice estimates or the Dini-derivative majorant; these become the seven children. In a scratch compile of the frozen Submission, all seven child types and the parent type elaborate in the comparator's child scope. The exact parent follows from slicing_mass_representation, slicing_representation_unique, slicing_mb_pointwise and slicing_mb_density_majorant with axioms [propext, Classical.choice, Quot.sound], and the dependency instantiations type-check. No proposed name occurs in the snapshot project or among the 200 DAG nodes. The active issue-676 configuration allows 1000 nodes at depth ≤ 6. The printed Simon text (4.9–4.11) matches the supplied proof.
