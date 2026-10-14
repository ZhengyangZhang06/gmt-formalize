# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.plane_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 1 (Simon Ch. 5, proof of 4.5, (1)–(2)). The parent applies this lemma with N := n + k, μ := R.measure, Q := approxTangentPlane n R.carrier, a := C₃δ^{2α}σⁿ, M := ω_nσⁿ/2 (density_bounds (b)), h₁ := C₃δ^α(2σ) (affine_approximation (4a)) and T₁ := T̃. Then h₁ + (4a/M)^{1/2}σ = (2C₃ + (8C₃/ω_n)^{1/2})δ^ασ = C₁₁δ^ασ, which is (2′). Notation: B := B_σ(ξ); for a subspace S' let τ_{S'}(x) := Σ_i|p_{Q(x)}e_i − p_{S'}e_i|² and J(S') := ∫⁻_B ofReal(τ_{S'}(x)) dμ.
0. Measurability. For every subspace S', x ↦ τ_{S'}(x) is μ-a.e. measurable. It is the composition of the μ-a.e. strongly measurable map x ↦ p_{Q(x)} with the continuous map L ↦ Σ_i|Le_i − p_{S'}e_i|² on continuous linear maps. Hence ofReal∘τ_{S'} is a.e.-measurable for μ restricted to B, and the lower integral is additive on such functions (lintegral_add_left′); constants pull out of lower integrals (lintegral_const_mul′).
Case 1: J(T) ≤ ofReal(a). Put S := T. Then S = T, J(S) ≤ ofReal(a) by the case assumption and J(S) ≤ J(T) trivially. It remains to prove the height bound.
1. By sibling proj_algebra (Submission.dorag_tes_projection_algebra), part (b), applied with the triple (Q(x), T, T₁), for every x: c₀ ≤ 2τ_T(x) + 2τ_{T₁}(x), where c₀ := Σ_i|p_Te_i − p_{T₁}e_i|² ≥ 0 is a constant.
2. Integrating over B with step 0: ofReal(c₀)μ(B) = ∫⁻_B ofReal(c₀) dμ ≤ ∫⁻_B (2ofReal(τ_T) + 2ofReal(τ_{T₁})) dμ = 2J(T) + 2J(T₁) ≤ 2ofReal(a) + 2ofReal(a) = ofReal(4a).
3. Since ofReal(M) ≤ μ(B) we get ofReal(c₀M) = ofReal(c₀)ofReal(M) ≤ ofReal(c₀)μ(B) ≤ ofReal(4a). As 4a ≥ 0 this means c₀M ≤ 4a, i.e. c₀ ≤ 4a/M because M > 0. Hence c₀^{1/2} ≤ (4a/M)^{1/2}.
4. Σ_i|(p_{T₁} − p_T)e_i|² = Σ_i|p_{T₁}e_i − p_Te_i|² = c₀. Let x ∈ spt μ ∩ B and y := x − ξ, so |y| ≤ σ. Then y − p_Ty = (y − p_{T₁}y) + (p_{T₁} − p_T)y. By the triangle inequality, the hypothesis on T₁, and proj_algebra (a) with A := p_{T₁} − p_T (in the form |Ay| ≤ |A||y|, the square root of (a)): |y − p_Ty| ≤ h₁ + c₀^{1/2}|y| ≤ h₁ + (4a/M)^{1/2}σ.
Case 2: J(T) > ofReal(a). Put S := T₁. Then J(S) ≤ ofReal(a) by hypothesis and J(S) ≤ ofReal(a) < J(T). For x ∈ spt μ ∩ B, |(x − ξ) − p_{T₁}(x − ξ)| ≤ h₁ ≤ h₁ + (4a/M)^{1/2}σ, since (4a/M)^{1/2} ≥ 0 and σ > 0.
The two cases are exhaustive, which proves the lemma. ∎

## Key steps

1. Case split on whether ∫_{B_σ(ξ)}|p_x − p_T|² ≤ a.
2. If yes, keep S = T: integrate |p_T − p_{T₁}|² ≤ 2|p_x − p_T|² + 2|p_x − p_{T₁}|² (proj_algebra (b)) and divide by μ(B_σ(ξ)) ≥ M, so |p_T − p_{T₁}|² ≤ 4a/M.
3. Then y − p_Ty = (y − p_{T₁}y) + (p_{T₁} − p_T)y, and proj_algebra (a) gives the height bound h₁ + (4a/M)^{1/2}σ.
4. If no, take S = T₁: its integral is ≤ a < the integral for T, and its height bound is h₁.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'tilt|harmonic approx|lipschitz approx|weakly harmonic|graph.*transfer|area formula' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT --glob '*.lean'`
- `rg -l -i 'weakly harmonic|rellich|harmonic approximation|tilt.excess' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory  (no match)`
- `rg -n --fixed-strings over /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for: lemma fderiv_const_smul_field; theorem addHaar_ball_of_pos; theorem norm_setIntegral_le_of_norm_le_const; theorem pow_rpow_inv_natCast; theorem withDensity_absolutelyContinuous; theorem ae_restrict_iff'; theorem toDual_symm_apply; theorem EuclideanSpace.inner_single_right; theorem measurable_fderiv_apply_const; lemma IntegrableOn.of_bound; theorem integral_finsetSum; theorem norm_fderiv_le_of_lipschitz; theorem integral_eq_lintegral_of_nonneg_ae; theorem toReal_le_of_le_ofReal; theorem lintegral_mono_set; theorem adjoint_inner_left`
- `lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace) on /tmp/tes-v2/chk/AreaChk.lean: #check/#print axioms Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn and areaJacobianAt_sq_eq_det_adjoint_comp`
- `git log --all -G '^import Poincare.SimonGMT' -- GMT/Ch07/Submission.lean; git show 77fcc7d -- GMT/Ch07/Submission.lean | grep '^+import'`
- `python3 -I: lean_name scan for dorag_tes_* over every workspace runs/*/dag.json and this run's nodes/; frozen sibling lean_statement comparison dag.json vs nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json; lean_contract.validate_lean_statement on the 8 v2 types`
- `lean on /tmp/tes-v2/lean/Integrals.lean (integral-scope dump) and /tmp/tes-v2/lean/Challenge_<key>.lean (8 comparator-format modules)`
- `lean on /tmp/tes-v2/asm/GWH.lean and /tmp/tes-v2/asm/Final.lean with #print axioms Asm.C_graph_weak_harmonic and #print axioms Asm.parent`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af4665598c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af4665598c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af4665598c/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json`
- `/tmp/tes-v2/lean/Integrals.lean`
- `/tmp/tes-v2/asm/GWH.lean`
- `/tmp/tes-v2/asm/Final.lean`
- `/tmp/tes-v2-review/Parens.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so every child type was checked in the correct compiler context.

Nothing in the snapshot proves the selected theorem or any child:
- GMT/Ch05 has only unproved Prop definitions for a different varifold type (TiltExcessHeightEstimate, LipschitzApproximationLemma, HarmonicApproximationLemma, TiltExcessDecayTheorem, …), used only in main_theorem := by sorry.
- GMT/Ch02 states the area formula as a contract.
- The weakly-harmonic/Rellich/tilt-excess search over Mathlib Analysis and MeasureTheory found no match.
So the split stands, and no identical comparator-approved declaration exists to reuse.

Usable infrastructure:
- The pinned SimonGMT area formula, weighted_area_formula_lipschitz_injOn, with only standard axioms.
- The Mathlib lemmas the v2 assembly uses, all present at the cited paths: fderiv_const_smul_field, Measure.addHaar_ball_of_pos, norm_setIntegral_le_of_norm_le_const, Real.pow_rpow_inv_natCast, withDensity_absolutelyContinuous, ae_restrict_iff', InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right, measurable_fderiv_apply_const, IntegrableOn.of_bound, integral_finsetSum.

Lean results:
- All 8 v2 child types elaborate in comparator scope, and their integral scopes are as intended.
- graph_weak_harmonic is proved from the corrected graph_transfer and graph_variation.
- The exact frozen parent type is proved from the 8 frozen sibling types and the v2 child types. Axioms: propext, Classical.choice, Quot.sound and the assumed contracts only; no sorryAx.

No dorag_tes_* name is reserved in any DAG.
