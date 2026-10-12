# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 9, first half (Simon Ch. 5, proof of 4.5, (19)–(20)). Its ingredients: dist(x − τ, S) ≤ |f(v) − λ(v)| on the graph; F ∩ B_{θ′R₀}(τ) ⊆ Φ(Bⁿ_{θ′R₀}); μ⌞F ≤ Hⁿ⌞F where θ = 1; the area bound for the graph; and the bound off F through (2′) and (18′). The parent applies the lemma with t := θ′R₀, h₀ := C₁₁δ^ασ, and c, Λ from affine_assembly. In the conclusion the whole parameter-ball lower integral is multiplied by ofReal(1 + n2ⁿ), and the off-graph term ofReal((h₀ + |c| + ‖Λ‖t)²)·μ(B_t(τ) ∖ F) is added outside that integral and outside its coefficient. This matches the Lean type ofReal(1 + n * 2 ^ n) * (∫⁻ v in ball 0 t, …) + ofReal((h₀ + ‖c‖ + ‖Λ‖ * t) ^ 2) * R.measure (…).
Step 0 (frame). ι is injective, range ι ⊆ T and dim T = n, so range ι = T. Also range ι ⊥ range ι', with dimensions n and k, so ℝ^{n+k} = range ι ⊕ range ι' orthogonally and range ι' = T^⊥. Let P := ι^* and P' := ι'^* (adjoints). Every y satisfies y = ιPy + ι'P'y, |y|² = |Py|² + |P'y|² and p_Ty = ιPy, so |y − p_Ty| = |P'y|. Moreover P(ι'c) = 0 and P'(ι'c) = c. For x ∈ ℝ^{n+k} write x' := P(x − ξ) and x'' := P'(x − ξ). Then x − τ = ιx' + ι'(x'' − c), so |x'| = |P(x − τ)| ≤ |x − τ|.
Step 1 (dim S = n). L := ι + ι'∘Λ satisfies |Lw|² = |ιw|² + |ι'Λw|² = |w|² + |Λw|² ≥ |w|². So L is injective and dim S = dim range L = n (LinearMap.finrank_range_of_inj; finrank of ℝⁿ is n).
Step 2 (distance to S). For any x ∈ ℝ^{n+k}, the vector y₀ := Lx' = ιx' + ι'Λx' lies in S. The orthogonal projection gives the nearest point of S (Submodule.starProjection_minimal), so |(x − τ) − p_S(x − τ)| ≤ |(x − τ) − y₀| = |ι'(x'' − c − Λx')| = |x'' − c − Λx'|.
Step 3 (on the graph). Put d(x) := |(x − τ) − p_S(x − τ)|². If x = Φ(v), then x' = v and x'' = f(v), so d(Φ(v)) ≤ |f(v) − c − Λv|² for every v ∈ ℝⁿ by Step 2. If moreover x ∈ B_t(τ), then |v| = |x'| ≤ |x − τ| ≤ t. Hence F ∩ B_t(τ) ⊆ Φ(Bⁿ_t), with Bⁿ_t the closed ball of ℝⁿ.
Step 4 (off the graph). For x ∈ spt μ ∩ B_t(τ): |x''| = |(x − ξ) − p_T(x − ξ)| ≤ h₀ and |x'| ≤ t. By Step 2, d(x)^{1/2} ≤ |x''| + |c| + ‖Λ‖|x'| ≤ h₀ + |c| + ‖Λ‖t =: K.
Step 5 (multiplicity one). N := {x ∈ M ∩ B_t(τ) : θ(x) ≠ 1} is Borel with μ(N) = 0. Since θ ≥ 1 on M, Hⁿ(N) ≤ ∫_N θ dHⁿ = μ(N) = 0. Hence for every Borel S' ⊆ B_t(τ) and measurable h ≥ 0: ∫_{S'} h dμ = ∫_{S'∩M} θh dHⁿ = ∫_{S'∩M} h dHⁿ ≤ ∫_{S'} h dHⁿ.
Step 6 (estimate). d is continuous, so ofReal∘d is measurable. F is closed: x ∈ F ⇔ x'' = f(x'). Split B := B_t(τ) into B ∩ F and B ∖ F, so ∫⁻_B ofReal(d) dμ = ∫⁻_{B∩F} ofReal(d) dμ + ∫⁻_{B∖F} ofReal(d) dμ.
6.1 Off-graph part. μ(ℝ^{n+k} ∖ spt μ) = 0, so μ-a.e. x ∈ B ∖ F lies in spt μ, where d(x) ≤ K² by Step 4. Hence ∫⁻_{B∖F} ofReal(d) dμ ≤ ∫⁻_{B∖F} ofReal(K²) dμ = ofReal(K²)·μ(B ∖ F). This holds in [0, ∞] also when μ(B ∖ F) = ∞ or K = 0.
6.2 Graph part. By Step 5, then Step 3 with monotonicity in the domain, then sibling graph_area (Submission.dorag_tes_lipschitz_graph_area_bounds), upper bound with A := Bⁿ_t (Borel) and h := ofReal∘d:
 ∫⁻_{B∩F} ofReal(d) dμ ≤ ∫⁻_{B∩F} ofReal(d) dHⁿ ≤ ∫⁻_{Φ(Bⁿ_t)} ofReal(d) dHⁿ ≤ ∫⁻_{Bⁿ_t} ofReal(1 + 2ⁿΣ_i|Df(v)e_i|²)·ofReal(d(Φ(v))) dv.
 Since f is 1-Lipschitz, ‖Df(v)‖ ≤ 1 and so Σ_i|Df(v)e_i|² ≤ n for every v (Df(v) = 0 where f is not differentiable). By Step 3 the last integral is ≤ ofReal(1 + n2ⁿ)·∫⁻_{Bⁿ_t} ofReal(|f(v) − c − Λv|²) dv (lintegral_const_mul).
6.3 The sphere {|v| = t} is Lⁿ-null (MeasureTheory.Measure.addHaar_sphere, n ≥ 1), so the lower integral over Bⁿ_t equals the one over the open ball B̆ⁿ_t(0) (Lean ball 0 t).
6.4 Adding 6.1 and 6.2 (with 6.3): (∫⁻_{B_t(τ)} ofReal(d) dμ) ≤ ofReal(1 + n2ⁿ)·(∫⁻_{B̆ⁿ_t(0)} ofReal(|f(v) − c − Λv|²) dv) + ofReal((h₀ + |c| + ‖Λ‖t)²)·μ(B_t(τ) ∖ F). Here the off-graph term is a separate summand, outside the parameter-ball integral and its coefficient. Together with Step 1 this is the claim. ∎

## Key steps

1. Frame: range ι = T, ℝ^{n+k} = range ι ⊕ range ι', coordinates x' = ι^*(x − ξ), x'' = ι'^*(x − ξ), and |x'| ≤ |x − τ|.
2. L = ι + ι'Λ is injective, so dim S = n.
3. dist(x − τ, S) ≤ |x'' − c − Λx'|. This equals |f(v) − c − Λv| on the graph and is ≤ K := h₀ + |c| + ‖Λ‖t on spt μ ∩ B_t(τ).
4. F ∩ B_t(τ) ⊆ Φ(Bⁿ_t), and μ ≤ Hⁿ on B_t(τ) ∩ F because θ = 1 a.e. and θ ≥ 1 on M.
5. Graph part: the graph_area upper bound with Σ_i|Df e_i|² ≤ n gives ≤ ofReal(1 + n2ⁿ)·(∫⁻_{B̆ⁿ_t}|f − c − Λ|²). Off-graph part: ≤ ofReal(K²)·μ(B_t(τ) ∖ F), added as a separate summand outside the integral.

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
