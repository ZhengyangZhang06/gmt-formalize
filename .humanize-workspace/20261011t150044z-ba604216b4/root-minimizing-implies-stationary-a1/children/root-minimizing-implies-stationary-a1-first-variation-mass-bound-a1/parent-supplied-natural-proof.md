# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 4, 2.2 and Ch. 2, 5.2–5.3 (the area formula expresses the mass of φ_{t#} as ∫ θJ^Mφ_t and J^Mφ_t = 1 + t div_M X + o(t)); this is step 5 of the parent proof, in the one-sided form that suffices for minimality. Write CB for the sibling covectorEuclideanNorm_gram_bounds and TM for the sibling imrep_approxTangent_starProjection_aesm. Notation: K := tsupport X ⊆ W, Q(x) := approxTangentPlane n M x, p(x) its projection, div_M X(x) := tangentialDivergence n M X x = trace(p(x)DX(x)), m := (R.measure W).toReal = ∫_{M∩W} θ dH^n, A := sup_x ‖DX(x)‖ < ∞, and R.firstVariation X = ∫_M θ div_M X dH^n.
1. Good points. For H^n-a.e. x ∈ M there are an orthonormal basis τ = (τ_1, …, τ_n) of an approximate tangent plane and s = ±1 with ξ(x)(β) = s·β(τ) for all n-covectors β (R.orients); by uniqueness that plane is Q(x), and then div_M X(x) = Σ_a τ_a·DX(x)τ_a (trace of p(x)DX(x) computed in an orthonormal basis of ℝ^P adapted to Q(x)).
2. Jacobian inequality. For a linear map L and orthonormal τ_1, …, τ_n let G := (Lτ_a·Lτ_b)_{a,b}, a positive semidefinite matrix. If λ_1, …, λ_n ≥ 0 are its eigenvalues then det G = Πλ_a ≤ Π e^{λ_a − 1} = exp(tr G − n) (as λ ≤ e^{λ−1}), and tr G = Σ_a |Lτ_a|². Take L = I + tDX(x) + E with ‖E‖ ≤ η|t|, η ≤ 1, |t| ≤ 1. Then |Lτ_a|² = 1 + 2tτ_a·DX(x)τ_a + 2τ_a·Eτ_a + |tDX(x)τ_a + Eτ_a|² ≤ 1 + 2tτ_a·DX(x)τ_a + 2η|t| + (A + 1)²t², so (det G)^{1/2} ≤ exp(σ) with σ := t·div + nη|t| + n(A+1)²t²/2, where div := Σ_a τ_a·DX(x)τ_a. Put c_0 := (n + 1)(A + 2 + (A+1)²) > 0. Then |σ| ≤ |t|c_0 ≤ 1 for |t| ≤ 1/c_0, and e^σ ≤ 1 + σ + σ² for |σ| ≤ 1, so: (det G)^{1/2} ≤ 1 + t·div + |t|(nη + n(A+1)²|t|/2 + c_0²|t|). Hence, given ε' > 0, choosing η := min(1, ε'/(2n + 1)) and then |t| small, (det G)^{1/2} ≤ 1 + t·div + ε'|t| uniformly in x and τ. (For n = 0 both sides reduce to det of the empty matrix, 1 ≤ 1 + ε'|t|.)
3. Choice of δ. Given ε > 0 put ε' := ε/(m + 1), η as in step 2, and choose δ ∈ (0, 1] with δ ≤ δ(η) from the hypothesis, δ ≤ 1/c_0, δ·(n(A+1)²/2 + c_0²) ≤ ε'/2 and δ·(nA + ε') ≤ 1, so that step 2 yields (det G)^{1/2} ≤ 1 + t·div + ε'|t| for |t| < δ (and 1 + t·div_M X + ε'|t| ≥ 0).
4. Pointwise bound. Fix |t| < δ, S as in the statement and an admissible ω (ω ∈ 𝒟^n(U), tsupport ω ⊆ W, |ω(y)|_E ≤ 1 for all y). Let g(x) := θ(x)ξ(x)(ω(φ_t x)∘Dφ_t(x)), so S(ω) = ∫_M g dH^n. At a good point x ∈ M ∩ W: g(x) = sθ(x)·ω(φ_t x)(Dφ_t(x)τ_1, …, Dφ_t(x)τ_n), so by CB(1) and step 2 (with L = Dφ_t(x), E := Dφ_t(x) − I − tDX(x), ‖E‖ ≤ η|t|): |g(x)| ≤ θ(x)·|ω(φ_t x)|_E·(det G)^{1/2} ≤ θ(x)(1 + t·div_M X(x) + ε'|t|). At a good point x ∈ M ∖ W: x ∉ K, so φ_t(x) = x ∉ W ⊇ tsupport ω and g(x) = 0. Hence g ≤ h a.e. on M, where h := 1_W·θ·(1 + t·div_M X + ε'|t|).
5. Integration. g is a.e. strongly measurable (θ measurable, ξ a.e. strongly measurable, x ↦ ω(φ_t x) continuous, x ↦ fderiv ℝ (φ_t) x measurable by Mathlib measurable_fderiv) and |g| ≤ θ·1_W·(1 + |t|(nA + ε')), which is integrable because ∫_{M∩W} θ = m < ∞; h is integrable because div_M X is H^n⌞M-a.e. strongly measurable (TM: it is the trace of p(x)∘DX(x), a continuous function of (p(x), DX(x))) and bounded by nA. Therefore S(ω) ≤ ∫_M h dH^n = m + t∫_{M∩W} θ div_M X dH^n + ε'|t|m. Since DX(x) = 0 on the open set ℝ^P ∖ K, div_M X vanishes off K ⊆ W, so ∫_{M∩W} θ div_M X = R.firstVariation X. With ε'm ≤ ε: S(ω) ≤ m + t·R.firstVariation X + ε|t|.
6. Conclusion. ofReal is monotone, so ofReal(S ω) ≤ ofReal(m + t·R.firstVariation X + ε|t|) for every admissible ω, and taking the supremum, S.massOn W ≤ ENNReal.ofReal((R.measure W).toReal + t·R.firstVariation X + ε|t|).

## Key steps

1. CB(1) bounds the integrand by θ·|ω|_E·(det Gram(Dφ_tτ))^{1/2}.
2. det G ≤ exp(tr G − n) and the expansion Dφ_t = I + tDX + o(t) give (det G)^{1/2} ≤ 1 + t div_M X + ε'|t| uniformly.
3. φ_t = id off spt X ⊆ W kills the integrand off W; integrate (measurability from TM) and take the supremum over admissible forms.

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
