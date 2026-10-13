# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 9. It uses three facts: p_α^#((div g) dy) = d(p_α^#γ); the Leibniz rule d(bβ) = db∧β + b dβ; and the bounds |p_α^#γ| ≤ |g| and |db∧p_α^#γ| ≤ C|db|. Here η = b·p_α^#γ with γ = Σ_j g_j ε_j is written intrinsically as η(x) = b(x)·(θ contracted with G(x)), where G = ι∘g∘p is a vector field. The constants need not be sharp.
Notation:
- n := m + 1; e_i := EuclideanSpace.single i 1 in ℝ^P; |·| := covectorEuclideanNorm; ‖·‖ is the operator norm on covectors.
- p : ℝ^P → ℝⁿ, p(x) := WithLp.toLp 2 (fun k => x (I k)), is continuous linear. ι : ℝⁿ → ℝ^P, ι(y) := Σ_k y_k•e_{I k}, is continuous linear.
- Since I is injective, p(ι(y)) = y and ‖ι(y)‖ = ‖y‖, because the e_{I k} are orthonormal.
- D(u) := det(Matrix.of fun k j => u j k) for u : Fin n → ℝⁿ. By hypothesis θ(w) = D(p ∘ w) for w : Fin n → ℝ^P.
- For a continuous alternating map α in k ≥ 1 variables and u ∈ ℝ^P, α.curryLeft u is the (k−1)-covector v ↦ α(Fin.cons u v), and ‖α.curryLeft u‖ ≤ ‖α‖‖u‖.
Facts.
(F1) For every k-covector α on ℝ^P, |α| ≤ P^k‖α‖. Each |α(e_J)| ≤ ‖α‖Π_i‖e_{J i}‖ = ‖α‖, and there are at most P^k tuples J. So |α|² ≤ P^k‖α‖², and |α| ≤ P^k‖α‖ (when P = 0 and k ≥ 1 there are no tuples and |α| = 0).
(F2) For every n-covector α, w : Fin n → ℝ^P, u ∈ ℝ^P and i ∈ Fin n: (−1)^i α(Fin.cons u (i.removeNth w)) = α(Function.update w i u). Indeed Function.update w i u = Fin.insertNth i u (i.removeNth w) (Fin.insertNth_removeNth). Moving the entry in position i to position 0 is a cyclic permutation of sign (−1)^i (ContinuousAlternatingMap.map_insertNth or AlternatingMap.map_perm).
(F3) (Jacobi.) For every linear A : ℝⁿ → ℝⁿ and u : Fin n → ℝⁿ, Σ_i D(Function.update u i (A(u i))) = tr(A)·D(u).
 - Φ(u) := Σ_i D(update u i (A(u i))) is multilinear in u.
 - Φ is alternating. If u_j = u_l with j ≠ l, the terms with i ∉ {j, l} contain two equal columns and vanish. The terms i = j and i = l are exchanged by swapping columns j and l, so they cancel.
 - An alternating n-linear form on ℝⁿ equals its value at the standard basis times D (AlternatingMap.eq_smul_basis_det).
 - At the standard basis e' of ℝⁿ, D(update e' i (A e'_i)) is the determinant of the identity matrix with its i-th column replaced by A e'_i. Expanding along row i (the other rows are rows of the identity), it equals (A e'_i)_i. So Φ(e') = Σ_i (A e'_i)_i = tr(A) (LinearMap.trace_eq_matrix_trace with the standard basis).
Construction.
- Let β₀ := sup_x |b(x)| and β₁ := sup_x ‖Db(x)‖; both are finite because b and Db are continuous with compact support. Put K := (P^m·β₀ + P^n·n·β₁)·‖θ‖. K does not depend on g.
- Now let g : ℝⁿ → ℝⁿ be C^∞ with ‖g‖ ≤ 1, and let G := ι ∘ g ∘ p : ℝ^P → ℝ^P. G is C^∞, ‖G(x)‖ = ‖g(p x)‖ ≤ 1, and DG(x) = ι ∘ Dg(p x) ∘ p.
- η(x) := b(x)•θ.curryLeft(G(x)), an element of Covector (Euclid P) m.
- ζ(x) := exteriorDerivative η x − (b(x)·tr(Dg(p x)))•θ, where tr(Dg(p x)) = LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (p x)).
1. (η is a test form in tsupport b.) x ↦ θ.curryLeft(G x) is C^∞, since G is C^∞ and u ↦ θ.curryLeft u is continuous linear. So η is C^∞. η(x) = 0 whenever b(x) = 0, so tsupport η ⊆ tsupport b, which is compact. Hence IsTestForm η.
2. (Derivative of η.) Fix x and w : Fin n → ℝ^P. Since η is differentiable, the exterior derivative formula (Poincare.SimonGMT.Chapter06.exteriorDerivative_apply) gives exteriorDerivative η x w = Σ_i (−1)^i D_x[η(·)(i.removeNth w)](w i). Here η(y)(i.removeNth w) = b(y)·θ(Fin.cons (G y) (i.removeNth w)), and u ↦ θ(Fin.cons u v) is linear. By the product and chain rules, its derivative at x in direction w i is Db(x)(w i)·θ(Fin.cons (G x) (i.removeNth w)) + b(x)·θ(Fin.cons (DG(x)(w i)) (i.removeNth w)). Hence exteriorDerivative η x w = Z_x(w) + b(x)·S_x(w), with
 - Z_x(w) := Σ_i (−1)^i Db(x)(w i)·θ(Fin.cons (G x) (i.removeNth w));
 - S_x(w) := Σ_i (−1)^i θ(Fin.cons (DG(x)(w i)) (i.removeNth w)).
3. (S_x = tr(Dg(p x))·θ.) Let A := Dg(p x) and u := p ∘ w. By (F2), S_x(w) = Σ_i θ(update w i (DG(x)(w i))). Now θ = D(p ∘ ·), p ∘ update w i v = update (p ∘ w) i (p v), and p(DG(x)(w i)) = p(ι(A(p(w i)))) = A(u i). So S_x(w) = Σ_i D(update u i (A(u i))) = tr(A)·D(u) = tr(A)·θ(w) by (F3).
4. (ζ(x) = Z_x, and ζ is a test form in tsupport b.) By steps 2–3 and the definition of ζ, ζ(x)(w) = Z_x(w) for all w. ζ is C^∞: exteriorDerivative η is C^∞ because η is a C^∞ form, and x ↦ b(x)·tr(Dg(p x)) is C^∞ because g is C^∞ and the trace is continuous linear. If x ∉ tsupport b, then b vanishes on a neighbourhood of x, so Db(x) = 0 and ζ(x) = Z_x = 0. Thus tsupport ζ ⊆ tsupport b, which is compact, and IsTestForm ζ.
5. (Bounds.) For all x, ‖η(x)‖ ≤ |b(x)|·‖θ‖·‖G(x)‖ ≤ β₀‖θ‖. Each of the n terms of Z_x(w) is bounded by ‖Db(x)‖‖w i‖·‖θ‖‖G x‖Π_{j≠i}‖w j‖, so ‖ζ(x)‖ ≤ n·β₁‖θ‖. By (F1) with k = m and k = n, |η(x)| ≤ P^m β₀‖θ‖ ≤ K and |ζ(x)| ≤ P^n n β₁‖θ‖ ≤ K.
6. (Identity.) By the definition of ζ, exteriorDerivative η x = (b(x)·LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (p x)))•θ + ζ(x) for all x, where p(x) = WithLp.toLp 2 (fun k => x (I k)).
Thus K and, for each g, the forms η and ζ have all the required properties.

## Key steps

1. Take η(x) = b(x)·θ.curryLeft(G(x)) with G = ι∘g∘p_I; it is a test form supported in tsupport b with |η| ≤ P^m sup|b|‖θ‖.
2. The exterior-derivative formula and the product rule split dη(x) into Z_x (the db-term) plus b(x)·S_x.
3. S_x = tr(Dg(p_I x))·θ by moving insertions to the front (sign (−1)^i) and Jacobi's identity Σ_i det(u with A u_i in column i) = tr(A)·det(u).
4. ζ := dη − (b·div g∘p_I)θ equals Z_x, vanishes off tsupport b, and is bounded by P^n·n·sup‖Db‖‖θ‖, independently of g.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `rg -n 'cmr_|massRepresentation' local-references/123e8435b4a2469b/project -g '*.lean' (no match); python3 scan of dag.json lean_name for prefix cmr (none) and of lean_statement for rieszMeasure|C_c|CompactlySupportedContinuousMap|rnDeriv|withDensity|cutoff|exteriorDerivative|LinearMap.trace|Matrix.det`
- `rg -n 'theorem eLpNorm_le_eLpNorm_fderiv_one|theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem integral_rieszMeasure|theorem haveLebesgueDecomposition_add|theorem singularPart_eq_zero_of_ac|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|def toRealPositiveLinear|theorem eq_toRealPositiveLinear_toReal|theorem tendsto_measure_cthickening_of_isCompact|theorem integral_withDensity_eq_integral_toReal_smul|theorem one_of_mem_closedBall|theorem exists_contDiff_tsupport_subset' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'; rg -n 'singularPart_eq_zero_of_ac|rnDeriv_lt_top' .../Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `grep -n 'theorem simon_theorem_4_14_caratheodory|theorem simon_theorem_4_14_positive_envelope|def IsLocallyBoundedCcFunctional|vectorFunctionalEnvelopeMeasure_isRadon|radonCaratheodoryMeasure_apply|integral_radonCaratheodoryMeasure' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/*.lean; grep -rn 'NullMeasurable|caratheodory' SimonGMT; sed -n 1,120p Chapter06/Representation.lean`
- `python3 scan of the public-import closure of the contract imports (module headers, public imports only); lake env lean /tmp/cmr-split/T1.lean T2.lean T3.lean T4.lean T5.lean T8.lean (#check availability after import GMT.Ch07.Submission)`
- `lake env lean /tmp/cmr-split/Stmts.lean (12 frozen child types + parent_check assembly); lake env lean /tmp/cmr-split/PI.lean and /tmp/cmr-split/PII.lean (interface skeletons); lake env lean /tmp/cmr-split/T6.lean T7.lean (#synth MeasurableSpace/BorelSpace/MeasureSpace on EuclideanSpace, toLp coordinate rfl, trace = sum of partials)`
- `read parent-child-handoff.json of dor_ims_sua_mollify_unit_field, rsd_mw_exists_testForm_approx, covectorEuclideanNorm_gram_bounds; check status accepted and candidate_commit in dag.json`
- `sed -n 75,110p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; sed -n 1800,1870p runtime.py; sed -n 555,640p verifier/gmt-compare.py; git show --stat 8abce3204fc05f00ae9a4047981f27a9f9a6ba3b`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/GeneralDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-b62f226305/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cmr-split/Stmts.lean`
- `/tmp/cmr-split/PI.lean`
- `/tmp/cmr-split/PII.lean`
- `/tmp/cmr-split/T1.lean`
- `/tmp/cmr-split/T2.lean`
- `/tmp/cmr-split/T3.lean`
- `/tmp/cmr-split/T4.lean`
- `/tmp/cmr-split/T5.lean`
- `/tmp/cmr-split/T6.lean`
- `/tmp/cmr-split/T8.lean`
- `/tmp/cmr-split/closure_pub.txt`

Pinned sources. The snapshot contract (manifest: project b4d606db, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. SimonGMT is pinned at 2b366308.

Not reachable. The proof cites the vector Riesz development (SimonGMT Chapter01 RadonPolarRepresentation, VectorFunctionalEnvelope, RadonCaratheodoryIntegral), Mathlib's Sobolev inequality (SobolevInequality.lean:439) and ContDiffBump.normed. All exist in the pinned sources, but none is in the public import closure of GMT.Ch07.Submission: lake env lean reports unknown identifiers. Leaf candidates may not add imports. Chapter06/Representation.lean only packages conditional MassRepresentation data and says the existence theorem is pending.

In scope and used:
- RealRMK.integral_rieszMeasure (RieszMarkovKakutani/Real.lean:345), with its IsFiniteMeasureOnCompacts and Regular instances;
- toRealPositiveLinear (Topology/ContinuousMap/CompactlySupported.lean:799);
- haveLebesgueDecomposition_add (Decomposition/Lebesgue.lean:115) and singularPart_eq_zero_of_ac (:252);
- integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318);
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Distribution/AEEqOfIntegralContDiff.lean:205);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- tendsto_measure_cthickening_of_isCompact (BorelSpace/Metric.lean:185);
- ContDiffBump (BumpFunction/Basic.lean:137);
- Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure;
- SimonGMT exteriorDerivative_apply, GeometricCurrentOn.le_massOn and boundary_apply.

Reuse. Three accepted DAG theorems are reused with identical frozen types: dor_ims_sua_mollify_unit_field, rsd_mw_exists_testForm_approx and covectorEuclideanNorm_gram_bounds. No cmr_ declaration exists in dag.json or in the snapshot.

Lean checks. All 12 child types elaborate after `import GMT.Ch07.Submission` in the comparator child scope. The selected type follows in Lean from cmr_exists_massRepresentation_core and cmr_null_of_representation. Skeletons of both assemblies typecheck against the sibling interfaces.
