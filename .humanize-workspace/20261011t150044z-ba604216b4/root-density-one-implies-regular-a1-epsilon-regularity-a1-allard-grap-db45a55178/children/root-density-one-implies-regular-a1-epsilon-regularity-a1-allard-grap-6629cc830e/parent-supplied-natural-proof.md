# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.c1_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 7 (mollification f_t := f∗ϱ_t; Df_t = (Df)∗ϱ_t = g∗ϱ_t on Ω_t by dominated convergence; Df_t → g locally uniformly; f_t → f; the limit theorem for derivatives). Smooth kernels are not needed: continuous compactly supported kernels suffice, and "f_t → f and Df_t → g locally uniformly ⇒ Df = g" is Mathlib's hasFDerivAt_of_tendstoLocallyUniformlyOn.
Notation: Df := fderiv ℝ f; N := {v ∈ Ω : f has no derivative g(v) at v}, Lⁿ(N) = 0.
1. (Reduction.) It suffices that f has derivative g(x) at every x ∈ Ω: then f is differentiable on Ω and fderiv ℝ f = g on Ω, which is continuous there, so ContDiffOn ℝ 1 f Ω (contDiffOn_succ_iff_fderiv_of_isOpen with 1 = 0 + 1, contDiffOn_zero).
2. (Kernels.) For t > 0, τ_t(y) := max(t − |y|, 0) is continuous, ≥ 0, vanishes for |y| ≥ t, has compact support and τ_t(0) = t ≠ 0, so I_t := ∫τ_t > 0. Put ϱ_t := τ_t/I_t: continuous, ≥ 0, ϱ_t(y) = 0 for |y| ≥ t, compactly supported, ∫ϱ_t = 1.
3. (Null sets pulled back.) For fixed x, y ↦ x − y preserves Lebesgue measure. Hence by Rademacher's theorem f is differentiable at x − y for a.e. y, and by hypothesis, for a.e. y, x − y ∈ Ω implies that f has derivative g(x − y) at x − y.
4. (Derivative of the mollification.) For t > 0 let f_t(x') := ∫ϱ_t(y)f(x' − y)dy and D_t(x) := ∫ϱ_t(y)Df(x − y)dy. For every x, y ↦ ϱ_t(y)Df(x − y) is integrable and f_t has Fréchet derivative D_t(x) at x: differentiate under the integral with a Lipschitz majorant (F(x', y) := ϱ_t(y)f(x' − y), F'(y) := ϱ_t(y)Df(x − y), bound Lϱ_t(y)): y ↦ F(x', y) is continuous with compact support; F' is measurable (measurability of fderiv); |F(a, y) − F(b, y)| ≤ Lϱ_t(y)|a − b|; Lϱ_t is integrable; and for a.e. y (step 3), x' ↦ ϱ_t(y)f(x' − y) has derivative ϱ_t(y)Df(x − y) at x by the chain rule.
5. (Identification.) If B_t(x) ⊆ Ω then ϱ_t(y)Df(x − y) = ϱ_t(y)g(x − y) for a.e. y (for |y| < t, x − y ∈ Ω ∖ N outside a null set, where Df = g; for |y| ≥ t both sides vanish). So D_t(x) = ∫ϱ_t(y)g(x − y)dy, and this integrand is integrable.
6. (Estimate.) If B_t(x) ⊆ Ω and |g(x − y) − g(x)| ≤ ε for |y| < t, then, since ∫ϱ_t = 1, D_t(x) − g(x) = ∫ϱ_t(y)(g(x − y) − g(x))dy has norm ≤ ∫ϱ_t(y)ε dy = ε.
7. (Local uniform convergence.) Let t_m := 1/(m + 1). Fix x₁ ∈ Ω, ρ₁ > 0 with B̆_{ρ₁}(x₁) ⊆ Ω and r := ρ₁/3, so B_{2r}(x₁) ⊆ Ω. g is uniformly continuous on the compact B_{2r}(x₁); for ε > 0 take δ > 0 with |g(u) − g(u')| < ε/2 for u, u' ∈ B_{2r}(x₁), |u − u'| < δ. If t_m < min(δ, r) and y ∈ B̆_r(x₁), then B_{t_m}(y) ⊆ B_{2r}(x₁) ⊆ Ω and, for |w| < t_m, |g(y − w) − g(y)| < ε/2; by step 6 |D_{t_m}(y) − g(y)| ≤ ε/2 < ε. So D_{t_m} → g locally uniformly on Ω.
8. (Pointwise convergence.) |f_t(x) − f(x)| = |∫ϱ_t(y)(f(x − y) − f(x))dy| ≤ ∫ϱ_t(y)Lt dy = Lt, so f_{t_m}(x) → f(x).
9. (Limit.) By the uniform-limit theorem for derivatives on the open set Ω (steps 4, 7, 8), f has derivative g(x) at every x ∈ Ω; step 1 concludes. ∎
Lean notes: Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero, HasCompactSupport.intro, integral_div; Measure.measurePreserving_sub_left … |>.quasiMeasurePreserving.ae; hasFDerivAt_integral_of_dominated_loc_of_lip (s := univ) with LipschitzOnWith.of_dist_le_mul; hasFDerivAt_sub_const and ContinuousLinearMap.comp_id; integral_congr_ae, integral_smul_const, integral_sub, norm_integral_le_of_norm_le, integral_mul_const; tendstoLocallyUniformlyOn_iff, IsCompact.uniformContinuousOn_of_continuous, Metric.uniformContinuousOn_iff, tendsto_one_div_add_atTop_nhds_zero_nat; hasFDerivAt_of_tendstoLocallyUniformlyOn. Pitfall: on Euclid-valued linear maps rw/simp with zero_smul can fail (WithLp/PiLp instance paths); use exact (zero_smul ℝ A).trans (zero_smul ℝ B).symm with explicit arguments. Reference implementation: a compiled proof of exactly this declaration (single theorem, default maxHeartbeats, no helper declarations or set_option, axioms propext/Classical.choice/Quot.sound, passes the leaf-delta rule) is in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/graph_c1_decomposition/GraphC1Full.lean (git-ignored scratch; same machine).

## Key steps

1. Reduce to HasFDerivAt f (g x) x for every x ∈ Ω (then fderiv = g is continuous, so C¹).
2. Continuous tent kernels ϱ_t ≥ 0 supported in B_t(0) with ∫ϱ_t = 1.
3. Differentiation under the integral: D(f∗ϱ_t)(x) = ∫ϱ_t(y)Df(x − y)dy (Rademacher + translation invariance).
4. On B_t(x) ⊆ Ω, Df(x − y) = g(x − y) a.e., so |D_t(x) − g(x)| ≤ sup_{|y|<t}|g(x − y) − g(x)| → 0 locally uniformly.
5. f_t → f pointwise; hasFDerivAt_of_tendstoLocallyUniformlyOn gives Df = g on Ω.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean  (all three e4148e7f9503aa28930a4e6a30b0aed205977718fd3c4d1938266b009467ef20)`
- `rg -n -i 'campanato' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory  (no match, exit 1); rg -n 'dorag|graph_slope|campanato' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT  (no match, exit 1)`
- `rg -n 'theorem hasFDerivAt_of_tendstoLocallyUniformlyOn' Analysis/Calculus/UniformLimitsDeriv.lean; rg -n 'theorem ae_tendsto_lintegral_enorm_sub_div|theorem ae_tendsto_average_norm_sub' MeasureTheory/Covering/Differentiation.lean; rg -n 'theorem tendsto_filterAt' MeasureTheory/Covering/Besicovitch.lean  (snapshot Mathlib)`
- `rg -n 'theorem measurable_fderiv\b' Analysis/Calculus/FDeriv/Measurable.lean; rg -n 'theorem continuousOn_extendFrom|theorem extendFrom_extends' Topology/ExtendFrom.lean; rg -n 'theorem hasFDerivAt_integral_of_dominated_loc_of_lip\b' Analysis/Calculus/ParametricIntegral.lean  (snapshot Mathlib)`
- `rg -n 'theorem starProjection_eq_self_iff|theorem inner_starProjection_left_eq_right|theorem starProjection_norm_le' Analysis/InnerProductSpace/Projection/Basic.lean; rg -n 'theorem ae_differentiableAt|theorem LipschitzWith.ae_differentiableAt' Analysis/Calculus/Rademacher.lean; rg -n 'theorem norm_fderiv_le_of_lipschitz\b' Analysis/Calculus/FDeriv/Basic.lean; rg -n 'theorem contDiffOn_succ_iff_fderiv_of_isOpen' Analysis/Calculus/ContDiff/*.lean  (snapshot Mathlib)`
- `rg -n 'euclideanHausdorffMeasure_eq_volume' MeasureTheory Geometry; rg -n "theorem lintegral_map'" MeasureTheory/Integral/Lebesgue/Map.lean; rg -n 'theorem le_iff\b' MeasureTheory/Measure/*.lean  (snapshot Mathlib); rg -n euclideanHausdorffMeasure_image_le_of_lipschitzOn /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean; grep -n import .../Chapter03/Rectifiable.lean`
- `python3 -I: lean_name scan of the 7 dorag_gc_* names over workspaces/gmt-ch0*/.humanize/github-theorem-prover/runs/*/dag.json (1616 nodes; no match); comparison of the four sibling stubs in GraphC1Full.lean with the dag.json lean_statement of tangent_projection_measurable, monotonicity, support_null, graph_tangent (all equal)`
- `python3 -I gmt-compare.child_modules (contract mode) → 8 Challenge_<key>.lean modules (7 children + parent); lean-4.35.0-rc3 with the built workspace LEAN_PATH on each (exit 0, only the sorry warning)`
- `python3 -I lean_contract.validate_lean_statement on the 7 child types; leaf_verification.check_source_delta for each child inserted alone before main_theorem (all pass)`
- `source GMT/Scratch/graph_c1_decomposition/env.sh; lean GraphC1Full.lean with #print axioms (exit 0, 120 s)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ExtendFrom.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/graph_c1_decomposition/GraphC1Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db45a55178/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db45a55178/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db45a55178/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical (sha256 e4148e7f…) to the workspace Contract and to Submission, which is the compiler context of every child type.

Nothing in the snapshot proves a child, so nothing can be reused: 'campanato' and the dorag/graph_slope names have no match (rg exit 1).

The pinned library supplies every API the child proofs use:
- hasFDerivAt_of_tendstoLocallyUniformlyOn (UniformLimitsDeriv.lean:396);
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (Differentiation.lean:818);
- Besicovitch.tendsto_filterAt (Besicovitch.lean:1060);
- measurable_fderiv (FDeriv/Measurable.lean:378);
- extendFrom_extends and continuousOn_extendFrom (ExtendFrom.lean:55, 61);
- hasFDerivAt_integral_of_dominated_loc_of_lip (ParametricIntegral.lean:163);
- Submodule.starProjection_eq_self_iff, starProjection_norm_le and inner_starProjection_left_eq_right (Projection/Basic.lean:290, 386, 652);
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
- contDiffOn_succ_iff_fderiv_of_isOpen (ContDiff/Defs.lean:891);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- lintegral_map' (Lebesgue/Map.lean:36);
- Measure.le_iff (CompleteLattice.lean:41);
- SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216), in the import closure via Chapter03/Rectifiable.

Lean checks:
- All 8 comparator-format challenge modules (7 children and the parent) elaborate.
- The complete development compiles; every child uses only propext, Classical.choice and Quot.sound.
- The parent assembly proves the exact frozen type from the children and the four sibling stubs, whose types equal the frozen DAG types.
- No dorag_gc_* name collides with any DAG reservation, so the v1 names are kept with identical types.
