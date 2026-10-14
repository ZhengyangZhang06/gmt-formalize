# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.pullback_continuity-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.pullback_continuity-a1.minor_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (bounds and measurability) of the supplied proof of the selected parent, cmcdt_lpi_pullback_weak_continuity. Here it is stated for one Lipschitz map with arbitrary rows a and columns b; the parent uses r := m, a := I and b := id.

Notation. Dv(u) := fderiv ℝ v u ∈ L(ℝ^m, ℝ^p), with the operator norm ‖·‖. e_t := EuclideanSpace.single t 1 ∈ ℝ^m, so ‖e_t‖ = 1. y_i is the i-th coordinate of y ∈ ℝ^p. For a continuous linear map A : ℝ^m → ℝ^p let Φ(A) be the r×r matrix with entries Φ(A)_{s,t} := (A e_{b(t)})_{a(s)}. Then M(u) = det Φ(Dv(u)).

1. (Measurability of the derivative.) ℝ^m and ℝ^p are finite-dimensional and ℝ^p is complete. So u ↦ Dv(u) is Borel measurable from ℝ^m to L(ℝ^m, ℝ^p) for every function v (Mathlib measurable_fderiv; no regularity of v is needed).
2. (Continuity of A ↦ det Φ(A).) Fix s, t. The entry A ↦ (A e_{b(t)})_{a(s)} is the evaluation A ↦ A e_{b(t)} (continuous: evaluation at a fixed vector, continuous_eval_const) followed by the coordinate y ↦ y_{a(s)} (the continuous linear functional EuclideanSpace.proj (a s)). Hence A ↦ Φ(A) is continuous into Matrix (Fin r) (Fin r) ℝ with the product topology (continuous_pi in both indices). The determinant is a polynomial in the entries, so A ↦ det Φ(A) is continuous (Continuous.matrix_det).
3. (Measurability of M.) M is the continuous map A ↦ det Φ(A) composed with the measurable map u ↦ Dv(u). Hence M is measurable. This is the first conjunct.
4. (Entry bound.) Fix u ∈ ℝ^m. Since v is L-Lipschitz, ‖Dv(u)‖ ≤ L (norm_fderiv_le_of_lipschitz; where v is not differentiable, Dv(u) = 0). For all s, t:
   |Φ(Dv(u))_{s,t}| = |(Dv(u)e_{b(t)})_{a(s)}| ≤ ‖Dv(u)e_{b(t)}‖ ≤ ‖Dv(u)‖·‖e_{b(t)}‖ = ‖Dv(u)‖ ≤ L.
   The first inequality holds because each coordinate of a Euclidean vector is bounded by its norm (PiLp.norm_apply_le). The second is the operator-norm bound (ContinuousLinearMap.le_opNorm).
5. (Leibniz bound.) Let A be a real r×r matrix and x ∈ ℝ with |A_{i,j}| ≤ x for all i, j.
   - By the Leibniz formula (Matrix.det_apply), det A = Σ_{σ ∈ Perm(Fin r)} sign(σ)·Π_i A_{σ(i), i}.
   - By the triangle inequality, and because sign(σ) = ±1, |det A| ≤ Σ_σ Π_i |A_{σ(i),i}|.
   - Each factor satisfies 0 ≤ |A_{σ(i),i}| ≤ x, so each product is at most x^r (finite products of nonnegative numbers are monotone).
   - There are r! permutations (Fintype.card_perm, with card (Fin r) = r). Hence |det A| ≤ r!·x^r.
6. (Conclusion.) Step 4 allows step 5 with A := Φ(Dv(u)) and x := L. This gives |M(u)| ≤ r!·L^r for every u, the second conjunct. Together with step 3 this proves the claim. For r = 0 the matrix is empty and det = 1 = 0!·L^0, which is also what step 5 gives. ∎

## Key steps

1. u ↦ fderiv ℝ v u is Borel (measurable_fderiv), and A ↦ det((A e_{b t})_{a s}) is continuous, so the minor is measurable.
2. Each entry satisfies |(Dv(u)e_{b t})_{a s}| ≤ ‖Dv(u)‖ ≤ L (coordinate ≤ norm, operator norm, norm_fderiv_le_of_lipschitz).
3. Leibniz formula with |sign σ| = 1 and r! permutations gives |det| ≤ r!·L^r.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed -n 1,80p GMT/Ch07/Submission.lean (namespace GMT.Ch07; open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; open Poincare.SimonGMT.Chapter06; Euclid P := EuclideanSpace ℝ (Fin P))`
- `grep -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' SimonGMT/Chapter06/Forms.lean and Mass.lean (Covector E n := E [⋀^Fin n]→L[ℝ] ℝ; DifferentialForm E n := E → Covector E n)`
- `grep -rn StrictMono lake-packages-25730c7c/simongmt/Poincare (only Mass.lean covectorEuclideanNorm; no covector coordinate-expansion lemma)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json for lean_statements containing Matrix.det together with Covector/DifferentialForm (found accepted dor_lmb_fcd_jwc_covector_det_expansion, accepted dor_lmb_fcd_jwc_minor_measurable_bound, and the unaccepted overlap dor_lmb_fcd_jacobian_weak_continuity)`
- `python3 scan of dag.json lean_names with prefixes cmcdt_lpi, minor_measurable, scalar_weak and pullback (no node uses cmcdt_lpi_pc_)`
- `git show 2c87728aa7637a3a07953c178f3e4f9547979008:GMT/Ch07/Submission.lean (accepted Submission.dor_lmb_fcd_jwc_covector_det_expansion with identical type and its proof)`
- `grep of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, existing_by_name reuse, _install_parent_supplied_child_handoff) and inherited.py (cited_inherited)`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: norm_fderiv_le_of_lipschitz, measurable_fderiv, Continuous.matrix_det, HasCompactMulSupport.uniformContinuous_of_continuous, UniformContinuous.comp_tendstoUniformly, Integrable.mul_bdd, norm_integral_le_of_norm_le, integral_finsetSum, tendsto_finsetProd, Continuous.bounded_above_of_compact_support, HasCompactMulSupport.comp_left, PiLp.norm_apply_le, Matrix.det_apply, Matrix.det_le, integral_const_mul, Metric.tendstoUniformly_iff, ContinuousEvalConst.continuous_eval_const, EuclideanSpace.proj (all found)`
- `grep -rn 'cmcdt_lpi_pc_|dor_lmb_fcd_jwc_covector_det_expansion|cmcdt_lpi_pullback_weak_continuity|cmcdt_lpi_minor_weak_continuity' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib (no match)`
- `#check @Matrix.det_le after import GMT.Ch07.Submission (unknown constant: Mathlib.LinearAlgebra.Matrix.AbsoluteValue is not imported)`
- `lake env lean /tmp/pbc/Final.lean (generated from the exact submitted lean_statement strings plus the DAG's frozen parent and minor_continuity types; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-d2560752b4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-d2560752b4/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-0bb9e2d51a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-0bb9e2d51a/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Monoid.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Hom/ContinuousEvalConst.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/tmp/pbc/Final.lean`
- `/tmp/pbc/gen/decomp.json`

The snapshot (project b4d606db, Mathlib 25730c7c) contains nothing to reuse here: no covector coordinate expansion, no Lipschitz-minor bound, and none of the cmcdt_lpi_pc_*, cmcdt_lpi_pullback or minor names (the targeted rg found no match). SimonGMT Forms.lean fixes Covector E n := E [⋀^Fin n]→L[ℝ] ℝ and DifferentialForm E n := E → Covector E n; in Mass.lean the only StrictMono use is covectorEuclideanNorm. The DAG has an accepted theorem of identical type for step 1, dor_lmb_fcd_jwc_covector_det_expansion (commit 2c87728a), which is reused as a child. The similar accepted dor_lmb_fcd_jwc_minor_measurable_bound uses derivatives of component functions, so it is not reused. The overlapping dor_lmb_fcd_jacobian_weak_continuity (smooth test forms, not accepted) cannot be reused. Every Mathlib tool cited by the child proofs exists in the snapshot: norm_fderiv_le_of_lipschitz, measurable_fderiv, Continuous.matrix_det, HasCompactSupport.uniformContinuous_of_continuous and HasCompactSupport.comp_left (to_additive), UniformContinuous.comp_tendstoUniformly, Metric.tendstoUniformly_iff, Integrable.mul_bdd, norm_integral_le_of_norm_le, integral_const_mul, integral_finsetSum, tendsto_finsetSum, Continuous.bounded_above_of_compact_support, PiLp.norm_apply_le, Matrix.det_apply, continuous_eval_const and EuclideanSpace.proj. Matrix.det_le exists in Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean but is not imported by GMT.Ch07.Submission, so minor_bound uses the Leibniz formula directly. All child types and the full parent assembly compile with axioms propext, Classical.choice and Quot.sound.
