# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2 §4 (definition of T_yM for an embedded submanifold, and its identification with Dψ(ℝ^d)); used in steps 3 and 6 of the parent proof.
1. Setup. Put y := ψ(v) ∈ W ∩ N and L := Dψ(v) = fderiv ℝ ψ v; since V is open and r ≥ 1, ψ is differentiable at v with derivative L. L is injective, so (finite dimension) there is c > 0 with |Lh| ≥ c|h| for all h ∈ ℝ^d; range L is a linear subspace, hence closed.
2. range L ⊆ T_yN. Let w = La. If a = 0, the constant curve γ ≡ y works (y ∈ N). Otherwise choose ρ > 0 with closedBall(v, ρ) ⊆ V and κ > 0 with κ|a| < ρ, and let σ(s) := κ·tanh(s/κ), a smooth function with σ(0) = 0, σ'(0) = 1 and |σ(s)| < κ. Put γ(s) := ψ(v + σ(s)a). Then v + σ(s)a ∈ V for all s, so γ is C^r (in particular C¹) on ℝ ⊇ (−1,1), γ(ℝ) ⊆ ψ(V) ⊆ N, γ(0) = y, and γ'(0) = Dψ(v)(σ'(0)a) = La = w. Hence w ∈ T_yN.
3. Embedding property. If z_k ∈ V and ψ(z_k) → y then z_k → v: the set K := {ψ(z_k) : k} ∪ {y} is compact and contained in W, so V ∩ ψ^{-1}(K) is compact and contains every z_k; any cluster point z ∈ V of (z_k) satisfies ψ(z) = y = ψ(v) by continuity, so z = v by injectivity on V; hence z_k → v.
4. T_yN ⊆ range L. Let w ∈ T_yN, witnessed by γ. As γ is continuous at 0 and W is open, there is s_0 ∈ (0,1) with γ(s) ∈ W ∩ N = ψ(V) for |s| < s_0; write γ(s) = ψ(β(s)) with β(s) ∈ V (unique by injectivity). By step 3 (applied along sequences s_k → 0), β(s) → v as s → 0.
5. Write ψ(z) − y = L(z − v) + ρ(z) with |ρ(z)| ≤ η(|z − v|)·|z − v|, η(t) → 0 as t → 0. For |s| small, η(|β(s) − v|) ≤ c/2, hence |γ(s) − y| ≥ c|β(s) − v| − (c/2)|β(s) − v|, i.e. |β(s) − v| ≤ (2/c)|γ(s) − y|. Since γ is differentiable at 0, |γ(s) − y| ≤ C|s| for small |s|; thus |β(s) − v| = O(|s|) and |ρ(β(s))| = o(|s|).
6. Hence (γ(s) − y)/s = L((β(s) − v)/s) + o(1), so the difference quotients lie within o(1) of range L. Letting s → 0, w = γ'(0) belongs to the closure of range L, which is range L. Together with step 2, tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v).

## Key steps

1. Curves s ↦ ψ(v + σ(s)a) with σ smooth, bounded, σ'(0) = 1 show range Dψ(v) ⊆ T_{ψ(v)}N.
2. Properness and injectivity make ψ^{-1} continuous at ψ(v) along N ∩ W.
3. Injectivity of Dψ(v) gives |β(s) − v| = O(|γ(s) − ψ(v)|), so difference quotients of any curve in N lie in range Dψ(v) up to o(1).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `python3 -I: list dag.json node ids and lean_name (56 nodes; no collision with the twelve child names)`
- `grep -n 'exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' -A 25 mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `grep -rn 'theorem LinearMap.exists_antilipschitzWith' mathlib/Mathlib`
- `grep -n 'def normDet\|normDet_of_subsingleton\|normDet_comp\|normDet_sq_eq_det_gram\|euclideanHausdorffMeasure_image' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `sed -n 1,100p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -n hausdorffMeasure_zero_singleton mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'MeasurableSet.image_of_continuousOn_injOn\|ae_tendsto_measure_inter_div\|hausdorffMeasure_image_le\|measurable_fderiv\|measurableSet_of_differentiableAt\|extDerivWithin_pullback\|det_isEmpty\|lintegral_iUnion\|to_localInverse\|toHomeomorph\|exists_isSubordinate' mathlib/Mathlib`
- `sed -n 1,420p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 1,140p simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean; grep -n areaJacobianAt simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `sed -n 60,110p simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean; sed -n 30,70p simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `sed -n 1,140p simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; sed -n 95,140p simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; sed -n 110,360p simongmt/Poincare/SimonGMT/Chapter06/Currents.lean; sed -n 25,125p simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `sed -n 1,75p book/chapter-07.txt; sed -n 400,440p book/chapter-06.txt; sed -n 760,880p book/chapter-06.txt`
- `lake env lean /tmp/mis-decomp-v2/Check.lean (import GMT.Ch07.Submission; 12 child types in namespace GMT.Ch07.Submission, minimizing_implies_stationary and a conditional assembly_check; #print axioms)`
- `lake env lean /tmp/mis-decomp-v2/Standalone.lean (same with the frozen contract inlined)`
- `lake env lean /tmp/mis-decomp-v2/Radius.lean (radius_check, pieces_check; #print axioms)`
- `lake env lean /tmp/mis-decomp-v2/Instances.lean (Gram Matrix.of, HasOrthogonalProjection instances, operator norm, μHE[0] singleton, normDet out of ℝ^0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/mis-decomp-v2/Check.lean`
- `/tmp/mis-decomp-v2/Standalone.lean`
- `/tmp/mis-decomp-v2/Radius.lean`
- `/tmp/mis-decomp-v2/Instances.lean`

The local snapshot (project b4d606d, Mathlib 25730c7c) has no counterpart for the contract's IMRep push-forward, first variation or mean curvature, so the twelve children are new. The library facts they reuse are the ones cited in the child proofs. The only blocking defect from v1 is confirmed and repaired. Mathlib's exists_partition_approximatesLinearOn_of_hasFDerivWithinAt takes r : (E →L[ℝ] F) → ℝ≥0 with rpos : ∀ A, r A ≠ 0, and the unit-sphere minimum used in v1 does not exist for n = 0. The fix sets m(A) = 1 for n = 0 (alternatively 1/K from LinearMap.exists_antilipschitzWith, which also covers subsingleton domains) and r = 1 on non-injective maps; rpos then holds for every A. pieces_check compiles the resulting bi-Lipschitz partition for all n and P using only propext, Classical.choice and Quot.sound. The n = 0 facts used in the new step 10 exist: Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton, LinearMap.normDet_of_subsingleton and Matrix.det_isEmpty. The upper-density lemma needs only real n ≥ 0, and the SimonGMT area lemmas have no rank hypothesis and accept arbitrary weights. All twelve child types (eleven identical to v1) elaborate after import GMT.Ch07.Submission and also with the contract inlined. minimizing_implies_stationary compiles from them, and the conditional assembly uses only standard axioms. Inferred instances were verified: Matrix.of Gram matrix, Submodule.HasOrthogonalProjection.ofCompleteSpace and ContinuousLinearMap.hasOpNorm. No child name collides with any of the 56 DAG nodes.
