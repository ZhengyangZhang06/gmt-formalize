# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Steps 4(a)–4(d): the identity 4.11 for the smooth approximations f_σ of the Lipschitz function f (Simon: “To handle general Lipschitz f we simply use f^{(σ)} in place of f … then let σ ↓ 0”), the bound (4c), and the passage σ ↓ 0 (4d), for a fixed cut-off χ. Here the approximations are the functions g_j of the sibling `slicing_mb_smooth_approx` with accuracy δ_j = 1/(j+1) on K, in place of f_σ with accuracy Lσ.

Setting. P, m ∈ ℕ; U ⊆ ℝ^P; T ∈ D_{m+1}(U); (μ, v) with IsMeasureRepresentation T μ v, μ(K′) < ∞ for every compact K′ ⊆ U, and |v(x)(α)| ≤ |α| for all x, α (|·| = covectorEuclideanNorm); (μ₁, v₁) with IsMeasureRepresentation T μ₁ v₁; (μ₂, v₂) with IsMeasureRepresentation ∂T μ₂ v₂ (∂T = T.boundary ∈ D_m(U)); f : ℝ^P → ℝ L-Lipschitz on U; W ⊆ U open; LW ≥ 0 with ‖Df(x)‖ ≤ LW for Lebesgue-a.e. x ∈ W; ω ∈ D^m(U) with K := tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x; χ : ℝ → ℝ C^∞ with |χ| ≤ 1, |χ′| ≤ c, and χ′(s) = 0 for s ∉ (t − h, t). Write dω := exteriorDerivative ω and
 I₂ := ∫ χ(f(x))·v₂(x)(ω(x)) dμ₂(x),  I₁ := ∫ χ(f(x))·v₁(x)(dω(x)) dμ₁(x).
Claim: ofReal|I₂ − I₁| ≤ ofReal(c)·LW·μ(K ∩ f⁻¹([t − h, t])).

1. (Preliminaries.) K is compact (ω has compact support) and K ⊆ W ⊆ U. f is L-Lipschitz on W, hence continuous on W. c ≥ |χ′(0)| ≥ 0. Since ω(x) = 0 and dω(x) = 0 for x ∉ K (tsupport dω ⊆ tsupport ω, `tsupport_exteriorDerivative_subset`), and v₂(x), v₁(x) are linear, the integrands of I₂ and I₁ vanish outside K. The functions x ↦ v₂(x)(ω(x)) and x ↦ v₁(x)(dω(x)) are μ₂- resp. μ₁-integrable, because ω ∈ D^m(U) and dω ∈ D^{m+1}(U) are test forms and IsMeasureRepresentation applies. Moreover x ↦ 1_K(x)·χ(f(x)) is Borel (f is continuous on the closed set K), and the integrand of I₂ equals 1_K(x)χ(f(x))·v₂(x)(ω(x)); hence it is a.e.-strongly measurable and, being dominated by |v₂(x)(ω(x))|, integrable; likewise for I₁. (Alternatively, let f̃ be a McShane extension of f|U (`LipschitzOnWith.extend_real`); f̃ is continuous on ℝ^P and the integrands of I₂, I₁ are unchanged when f is replaced by f̃, because they vanish off K and f̃ = f on K ⊆ U.)

2. (Smooth approximations.) For j ∈ ℕ let δ_j := 1/(j+1). Apply the sibling `slicing_mb_smooth_approx` to W, f (L-Lipschitz on W), LW, K and δ_j: there is a C^∞ function g_j : ℝ^P → ℝ with |g_j(x) − f(x)| ≤ δ_j and ‖Dg_j(x)‖ ≤ LW for every x ∈ K.

3. (Gradient of the multiplier.) ψ_j := χ ∘ g_j is C^∞ and, by the chain rule, Dψ_j(x) = χ′(g_j(x))·Dg_j(x), so ‖Dψ_j(x)‖ = |χ′(g_j(x))|·‖Dg_j(x)‖. Let E_j := K ∩ f⁻¹((t − h − δ_j, t + δ_j)). For x ∈ K: if g_j(x) ∉ (t − h, t) then χ′(g_j(x)) = 0 and Dψ_j(x) = 0; if g_j(x) ∈ (t − h, t) then ‖Dψ_j(x)‖ ≤ c·LW and, since |f(x) − g_j(x)| ≤ δ_j, t − h − δ_j < f(x) < t + δ_j, i.e. x ∈ E_j. Hence ‖Dψ_j(x)‖ ≤ c·LW·1_{E_j}(x) for every x ∈ K.

4. (4.11 with the bound (4c).) Apply the sibling `slicing_mb_leibniz_bound` to T, μ, v, ω and ψ_j: there are test forms η₁ʲ ∈ D^m(U), η₂ʲ ∈ D^{m+1}(U) with η₁ʲ(x) = ψ_j(x)ω(x), η₂ʲ(x) = ψ_j(x)dω(x) and
 ofReal|∂T(η₁ʲ) − T(η₂ʲ)| ≤ ∫⁻ ‖Dψ_j(x)‖₊·ofReal(|ω(x)|) dμ(x).
For x ∉ K the integrand is 0 (ω(x) = 0); for x ∈ K, ofReal(|ω(x)|) ≤ 1 and step 3 applies. Hence the right side is ≤ ∫⁻ ofReal(c)·LW·1_{E_j} dμ = ofReal(c)·LW·μ(E_j) (E_j is Borel, step 6).

5. (Evaluation through the representations.) By IsMeasureRepresentation ∂T μ₂ v₂ and linearity of v₂(x): ∂T(η₁ʲ) = ∫ v₂(x)(ψ_j(x)ω(x)) dμ₂ = ∫ χ(g_j(x))·v₂(x)(ω(x)) dμ₂ =: I₂ʲ. By IsMeasureRepresentation T μ₁ v₁: T(η₂ʲ) = ∫ χ(g_j(x))·v₁(x)(dω(x)) dμ₁ =: I₁ʲ. So step 4 reads
 ofReal|I₂ʲ − I₁ʲ| ≤ ofReal(c)·LW·μ(E_j) for every j.

6. (The sets E_j.) Each E_j = K ∩ (W ∩ f⁻¹((t − h − δ_j, t + δ_j))) is Borel: W ∩ f⁻¹(open) is open because f is continuous on the open set W (`ContinuousOn.isOpen_inter_preimage`), and K is closed. Since δ_j decreases, E_{j+1} ⊆ E_j. A point x lies in every E_j iff x ∈ K and t − h − δ_j < f(x) < t + δ_j for all j, i.e. iff x ∈ K and t − h ≤ f(x) ≤ t; so ⋂_j E_j = K ∩ f⁻¹([t − h, t]). Finally μ(E_0) ≤ μ(K) < ∞ (K compact ⊆ U). By continuity from above (`tendsto_measure_iInter_atTop`), μ(E_j) → μ(K ∩ f⁻¹([t − h, t])), and therefore ofReal(c)·LW·μ(E_j) → ofReal(c)·LW·μ(K ∩ f⁻¹([t − h, t])) (multiplication by the finite constant ofReal(c)·LW is continuous on [0,∞]).

7. (σ ↓ 0, here j → ∞, on the left side.) For x ∈ K, g_j(x) → f(x) (|g_j(x) − f(x)| ≤ δ_j → 0) and χ is continuous, so χ(g_j(x)) → χ(f(x)); for x ∉ K all integrands below vanish (step 1). Hence χ(g_j(x))·v₂(x)(ω(x)) → χ(f(x))·v₂(x)(ω(x)) and χ(g_j(x))·v₁(x)(dω(x)) → χ(f(x))·v₁(x)(dω(x)) for every x. The integrands are measurable (χ∘g_j is continuous and the second factors are integrable) and dominated by |v₂(x)(ω(x))| resp. |v₁(x)(dω(x))| (as |χ| ≤ 1), which are integrable (step 1). By dominated convergence (`tendsto_integral_of_dominated_convergence`), I₂ʲ → I₂ and I₁ʲ → I₁, so ofReal|I₂ʲ − I₁ʲ| → ofReal|I₂ − I₁|.

8. (Conclusion.) Passing to the limit j → ∞ in the inequality of step 5, using steps 6 and 7 (limits preserve ≤ in [0,∞]): ofReal|I₂ − I₁| ≤ ofReal(c)·LW·μ(tsupport ω ∩ f⁻¹([t − h, t])). ∎

## Key steps

1. Smooth approximations g_j of f on K = tsupport ω with |g_j − f| ≤ 1/(j+1) and ‖Dg_j‖ ≤ LW (sibling slicing_mb_smooth_approx).
2. ψ_j = χ∘g_j: ‖Dψ_j‖ ≤ c·LW·1_{E_j} on K with E_j = K ∩ f⁻¹((t−h−δ_j, t+δ_j)).
3. Sibling slicing_mb_leibniz_bound plus the representations of ∂T and T: |∫χ(g_j)v₂(ω)dμ₂ − ∫χ(g_j)v₁(dω)dμ₁| ≤ c·LW·μ(E_j).
4. j → ∞: dominated convergence on the left, continuity from above (μ(K) < ∞) on the right, ⋂E_j = K ∩ f⁻¹([t−h, t]).

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
