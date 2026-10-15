# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.proj_algebra-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 1 (|p_T − p_{T̃}|² ≤ 2|p_x − p_T|² + 2|p_x − p_{T̃}|² and dist(x − ξ, T) ≤ dist(x − ξ, T̃) + ‖p_T − p_{T̃}‖|x − ξ|), Step 4 (|p_xe_{n+j}| = |(p_x − p_T)e_{n+j}| ≤ |p_x − p_T|) and Step 5 (identity (11): p_Tp_x^⊥p_T = (p_T − p_x)p_x^⊥(p_T − p_x)); Simon Ch. 5, 4.4 and (10)–(11). Notation: for a continuous linear A put |A| := (Σ_i|Ae_i|²)^{1/2} ≥ 0.
1. Proof of (a). Let y ∈ V and y_i := ⟨y, e_i⟩. Since (e_i) is an orthonormal basis, y = Σ_i y_ie_i and Σ_i y_i² = |y|². By linearity Ay = Σ_i y_iAe_i. By the triangle inequality and the Cauchy–Schwarz inequality for finite sums, |Ay| ≤ Σ_i|y_i||Ae_i| ≤ (Σ_iy_i²)^{1/2}(Σ_i|Ae_i|²)^{1/2} = |y||A|. Both sides are nonnegative, so squaring gives |Ay|² ≤ |A|²|y|². We also record (a′): |Ay| ≤ |A||y|.
2. Proof of (b). Fix i and put u := p_Qe_i − p_Se_i and w := p_Qe_i − p_Te_i. Then p_Se_i − p_Te_i = w − u, and by the parallelogram law |w − u|² ≤ |w − u|² + |w + u|² = 2|w|² + 2|u|². Summing over i gives Σ_i|p_Se_i − p_Te_i|² ≤ 2Σ_i|p_Qe_i − p_Se_i|² + 2Σ_i|p_Qe_i − p_Te_i|².
3. Facts used below. Let B := p_Q − p_T (continuous linear). Then Be_i = p_Qe_i − p_Te_i, so |B|² = |p_Q − p_T|². For every y the vector y − p_Qy lies in Q^⊥ and p_Qy ∈ Q; p_T fixes every vector of T and annihilates every vector of T^⊥.
4. Proof of (c). Let a, b ∈ T. Since a − p_Qa ∈ Q^⊥ and p_Qb ∈ Q, ⟨a − p_Qa, p_Qb⟩ = 0, hence ⟨a − p_Qa, b⟩ = ⟨a − p_Qa, b − p_Qb⟩. Because p_Ta = a and p_Tb = b we have a − p_Qa = p_Ta − p_Qa = −Ba and b − p_Qb = −Bb. Therefore ⟨p_Qa, b⟩ − ⟨a, b⟩ = −⟨a − p_Qa, b⟩ = −⟨Ba, Bb⟩, and by Cauchy–Schwarz and (a′), |⟨p_Qa, b⟩ − ⟨a, b⟩| ≤ |Ba||Bb| ≤ (|B||a|)(|B||b|) = |p_Q − p_T|²|a||b|.
5. Proof of (d). Let e ∈ T^⊥. Then p_Te = 0, so p_Qe = p_Qe − p_Te = Be and, by (a), |p_Qe|² = |Be|² ≤ |B|²|e|² = |p_Q − p_T|²|e|². ∎

## Key steps

1. (a): expand y in the orthonormal basis, Ay = Σ y_iAe_i, then triangle inequality and Cauchy–Schwarz.
2. (b): parallelogram law |w − u|² ≤ 2|w|² + 2|u|² for each basis vector, then sum.
3. (c): for a, b ∈ T, ⟨p_Qa, b⟩ − ⟨a, b⟩ = −⟨a − p_Qa, b − p_Qb⟩ = −⟨(p_Q − p_T)a, (p_Q − p_T)b⟩, then Cauchy–Schwarz and (a).
4. (d): for e ∈ T^⊥, p_Qe = (p_Q − p_T)e, then (a).

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
