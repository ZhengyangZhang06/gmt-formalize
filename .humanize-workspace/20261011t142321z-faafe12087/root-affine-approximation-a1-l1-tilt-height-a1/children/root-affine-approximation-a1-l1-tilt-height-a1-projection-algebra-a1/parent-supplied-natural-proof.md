# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.l1_tilt_height-a1`
- Child DAG node: `root.affine_approximation-a1.l1_tilt_height-a1.projection_algebra-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the two linear-algebra facts used in the supplied proof: step 2 (Simon, Ch. 5, proof of Lemma 2.1, display (2): sum_{i>n} e^{ii} = (1/2)|p_{T_x M} - p_{R^n}|^2, using e^{ij} = e^{ji}, sum_j e^{ij} e^{jk} = e^{ik} and trace = n) and step 4 (||A|| <= |A|).

Setting: R^m = EuclideanSpace R (Fin m) with the standard orthonormal basis e_i := EuclideanSpace.single i 1 (i in Fin m); hsNormSq A = sum_i ||A e_i||^2 and hsNorm A = sqrt(hsNormSq A). Every linear subspace W of R^m is finite-dimensional, hence complete, so the orthogonal projection p_W := W.starProjection is defined. It is a continuous linear map with p_W o p_W = p_W, range W and kernel W^perp, and it is self-adjoint: <p_W u, v> = <u, p_W v> (Submodule.starProjection_isSymmetric). Moreover p_{W^perp} = I - p_W (Submodule.starProjection_orthogonal).

Part (i): operator norm <= Hilbert-Schmidt norm.
1. Let v in R^m have coordinates v_i. Then v = sum_i v_i e_i and ||v||^2 = sum_i v_i^2.
2. By linearity A v = sum_i v_i A e_i. The triangle inequality and the Cauchy-Schwarz inequality in R^m give
 ||A v|| <= sum_i |v_i| ||A e_i|| <= (sum_i v_i^2)^{1/2} (sum_i ||A e_i||^2)^{1/2} = ||v|| * hsNorm A.
3. Since hsNorm A >= 0 and ||A v|| <= hsNorm A * ||v|| for all v, the characterization of the operator norm (ContinuousLinearMap.opNorm_le_bound) gives ||A|| <= hsNorm A.

Part (ii): the trace identity. Let P, T be subspaces of R^m with dim P = dim T =: k, and write p := p_P, q := p_T.
4. trace p = k and trace q = k. Indeed p maps R^m into P and fixes every vector of P, so p is the projection onto P along ker p; such a projection has trace dim P (LinearMap.IsProj.trace; equivalently, in an orthonormal basis adapted to P (+) P^perp its matrix is diag(1,...,1,0,...,0) with dim P ones). The same holds for q.
5. For every linear map C of R^m, trace C = sum_i <e_i, C e_i>, because the trace is the sum of the diagonal entries of the matrix of C in the orthonormal basis (e_i) (LinearMap.trace_eq_sum_inner with the orthonormal basis EuclideanSpace.basisFun (Fin m) R, whose vectors are the e_i; that lemma lives in Mathlib.Analysis.InnerProductSpace.Trace, which Submission.lean may import since only the contract's definitions are frozen; alternatively LinearMap.trace_eq_matrix_trace with the standard basis). For a self-adjoint B this gives
 hsNormSq B = sum_i ||B e_i||^2 = sum_i <B e_i, B e_i> = sum_i <e_i, B (B e_i)> = trace(B o B).
6. B := p - q is self-adjoint (a difference of self-adjoint maps), and p o p = p, q o q = q, so
 B o B = p - p o q - q o p + q.
 Using trace(p o q) = trace(q o p) (LinearMap.trace_mul_comm / trace_comp_comm') and step 4,
 hsNormSq(p - q) = trace(B o B) = trace p + trace q - 2 trace(q o p) = 2k - 2 trace(q o p).
7. Since p_{T^perp} = I - q,
 trace(p_{T^perp} o p) = trace p - trace(q o p) = k - trace(q o p).
8. Comparing 6 and 7: trace(p_{T^perp} o p_P) = hsNormSq(p_P - p_T) / 2. In Lean form this is
 LinearMap.trace R (Rn m) (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) = hsNormSq (P.starProjection - T.starProjection) / 2. QED
(For m = 0 everything is 0 and both parts hold trivially; the argument above covers this case as well.)

## Key steps

1. ||A v|| <= sum_i |v_i| ||A e_i|| <= ||v|| hsNorm A by Cauchy-Schwarz, hence ||A|| <= hsNorm A.
2. trace p_P = dim P and trace p_T = dim T (trace of a projection equals the dimension of its range).
3. hsNormSq B = sum_i <e_i, B B e_i> = trace(B o B) for self-adjoint B = p_P - p_T, and B o B = p_P - p_P p_T - p_T p_P + p_T.
4. hsNormSq(p_P - p_T) = 2k - 2 trace(p_T p_P) and trace(p_{T^perp} p_P) = k - trace(p_T p_P), hence the identity.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `timeout 300 rg -n 'aal_l1th|l1_tilt|l1th' <snapshot>/project <snapshot>/mathlib`
- `rg -n 'theorem (dist_starProjection_eq_infDist|norm_sub_starProjection|starProjection_orthogonal|starProjection_orthogonal_val|starProjection_add_starProjection_orthogonal|orthogonalProjection_orthogonal|starProjection_apply_eq_zero_iff|starProjection_apply_mem|trace_starProjection|starProjection_isSymmetric|isSymmetric_starProjection|isIdempotentElem_starProjection|starProjection_idem)' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (trace_smulRight|IsProj.trace|trace_comp_comm|trace_mul_comm|trace_eq_sum_inner|trace_eq_sum_orthonormalBasis|trace_id|trace_one)|lemma (trace_smulRight|IsProj.trace|trace_eq_sum_inner)' <snapshot>/mathlib/Mathlib; rg -n 'starProjection.*trace|trace.*starProjection' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (LocallyIntegrableOn.integrableOn_compact_subset|integrableOn_iff_integrable_of_support_subset|setIntegral_le_integral|Measure.integrableOn_of_bounded|ae_restrict_mem₀|withDensity_absolutelyContinuous|withDensity_apply)|lemma measure_compl_support' <snapshot>/mathlib/Mathlib`
- `rg -n 'integrableOn_of_bounded|comp_aestronglyMeasurable₂' <snapshot>/mathlib/Mathlib; rg -n 'starProjection_norm_le|norm_starProjection_apply_le' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep -n '^theorem|^lemma|^protected theorem' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n 'theorem (integral_hasDerivAt_right|integral_hasStrictDerivAt_right)|theorem norm_fderiv_le_of_lipschitz|theorem contDiff_one_iff_deriv|theorem contDiffAt_norm|theorem contDiff_iff_contDiffAt|theorem integral_mono_on' <snapshot>/mathlib/Mathlib`
- `python3 -I scan of dag.json nodes[*] (lean_name, status) for collisions and sibling-branch statuses; grep -rl aal_l1th .humanize GMT`
- `python3 -I /tmp/l1th-decomp/scripts/gen.py (verifier/lean_contract.py validate_lean_statement + verifier/gmt-compare.py child_modules, contract scope)`
- `lean /tmp/l1th-decomp/children/*/NodeChallenge.lean and NodeSolution.lean against a scratch GMT.Ch05.Submission olean`
- `lean /tmp/l1th-decomp/src/Assembly3.lean (#print axioms aal_l1_tilt_height)`
- `lean /tmp/l1th-decomp/final/All3.lean (#print axioms for the 3 children and the parent)`
- `python3 -I /tmp/l1th-decomp/scripts/numcheck2.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-l1-tilt-height-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-smooth-cutoff-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-projection-algebra-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-height-field-divergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/l1th-decomp/src/Assembly3.lean`
- `/tmp/l1th-decomp/final/All3.lean`

**Snapshot and existing names**
- Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- 'aal_l1th|l1_tilt|l1th' has no match in the snapshot project or Mathlib.
- Mathlib has no ready-made lemma for the trace of a starProjection, so the trace identity is a genuine child obligation.

**Mathlib lemmas located** (paths under mathlib/Mathlib)
- Analysis/InnerProductSpace/Projection/Basic.lean:
  - starProjection_orthogonal_val (:203)
  - dist_starProjection_eq_infDist (:234)
  - starProjection_norm_le (:386)
  - norm_starProjection_apply_le (:411)
  - starProjection_isSymmetric (:658)
  - starProjection_apply_eq_zero_iff (:689)
- LinearAlgebra/Trace.lean: trace_mul_comm (:103), trace_comp_comm' (:265), trace_smulRight (:272), IsProj.trace (:327).
- Analysis/InnerProductSpace/Trace.lean: trace_eq_sum_inner (:25). This module is not imported by the contract, but Submission.lean may import it.
- Measure theory:
  - Measure/Support.lean: measure_compl_support (:202)
  - Measure/WithDensity.lean: withDensity_apply (:44), withDensity_absolutelyContinuous (:146)
  - Measure/Restrict.lean: ae_restrict_mem₀ (:637)
  - Function/LocallyIntegrable.lean: LocallyIntegrableOn.integrableOn_compact_subset (:122)
  - Integral/IntegrableOn.lean: integrableOn_iff_integrable_of_support_subset (:462), Measure.integrableOn_of_bounded (:716)
  - Integral/Bochner/Set.lean: setIntegral_congr_fun (:73), integral_indicator (:185), setIntegral_le_integral (:742)
  - Function/StronglyMeasurable/AEStronglyMeasurable.lean: Continuous.comp_aestronglyMeasurable₂ (:263)
- For the cutoff:
  - SmoothTransition.lean: one_of_one_le, zero_of_nonpos, le_one, nonneg, contDiff (:161-205)
  - IntervalIntegral/FundThmCalculus.lean: integral_hasDerivAt_right (:725)
  - ContDiff/Deriv.lean: contDiff_one_iff_deriv (:98)
  - InnerProductSpace/Calculus.lean: contDiffAt_norm (:154)
  - FDeriv/Basic.lean: norm_fderiv_le_of_lipschitz (:947)
  - ContDiff/Defs.lean: contDiff_iff_contDiffAt (:1103)

**Sibling branch**
- The root.tilt_excess_height_estimate-a1 branch has analogous, not yet accepted nodes. Their names are reserved, so unique aal_l1th_* names are used instead.
- Its reviewed constructions (the bump with c >= 1/3, the trace identity, the divergence formula) agree with the natural proofs given here.

**Lean verification**
- The three child types pass validate_lean_statement, and their generated NodeChallenge and NodeSolution modules compile.
- A sorry-free parent assembly compiles from the children plus aal_tangent_structure, whose exact frozen types appear as stubs.
- In the full scratch formalization, the children use only propext, Classical.choice and Quot.sound, and the parent's only remaining sorry is aal_tangent_structure.

**Numerical checks**
- c = 5/12.
- The trace identity, the divergence formula and the absorption inequality all hold.
