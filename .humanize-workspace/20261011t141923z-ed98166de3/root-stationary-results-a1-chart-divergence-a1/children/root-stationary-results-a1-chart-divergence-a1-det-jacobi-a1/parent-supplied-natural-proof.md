# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.chart_divergence-a1`
- Child DAG node: `root.stationary_results-a1.chart_divergence-a1.det_jacobi-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝᵈ := EuclideanSpace ℝ (Fin d) = Rn d with the standard inner product ⟨·,·⟩; L(E, F) := E →L[ℝ] F and L(ℝⁿ) := ℝⁿ →L[ℝ] ℝⁿ, a ring whose multiplication is composition (f * g = f ∘L g holds by rfl) with identity 1; for A ∈ L(ℝⁿ, ℝᴺ), A* := ContinuousLinearMap.adjoint A, so ⟨A* z, c⟩ = ⟨z, A c⟩ (ContinuousLinearMap.adjoint_inner_left) and ⟨c, A* z⟩ = ⟨A c, z⟩ (ContinuousLinearMap.adjoint_inner_right); G := A* ∘L A and G⁻¹ := Ring.inverse G; trace means LinearMap.trace ℝ ℝⁿ applied to the underlying linear map (.toLinearMap); e_l := EuclideanSpace.single l 1 (l ∈ Fin n) is the standard orthonormal basis of ℝⁿ (= EuclideanSpace.basisFun (Fin n) ℝ l). Every lemma cited below resolves after `import GMT.Ch02.Submission` (checked with #check).
Source: parent proof, step 7 (D_v(det G) = det G · trace(G⁻¹ D_v G)), isolated as the general Jacobi formula; Mathlib 25730c7c contains no derivative of det, but supplies Matrix.det_one_add_smul.
Setting. Fix n. Let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, the standard basis of ℝⁿ, and for T ∈ L(ℝⁿ) let [T] := LinearMap.toMatrix b b T (the matrix of T), whose (i, j) entry is the i-th coordinate of T(e_j).
1. (det is a polynomial in matrix entries.) For every T ∈ L(ℝⁿ), T.det = LinearMap.det T = Matrix.det [T] (LinearMap.det_toMatrix), and Matrix.det M = Σ_{σ ∈ Perm (Fin n)} sign σ • Π_i M (σ i) i (Matrix.det_apply).
2. (det is C¹; first conjunct.) For fixed i, j the map T ↦ [T] i j = (T e_j) i is a continuous linear functional on L(ℝⁿ) (evaluation at e_j, a continuous linear map L(ℝⁿ) → ℝⁿ, followed by the i-th coordinate, a continuous linear functional), hence C^∞ (ContinuousLinearMap.contDiff). Finite products and finite sums of C^∞ real functions are C^∞ (contDiff_prod, ContDiff.sum); the sign factor acts through ℤˣ, so rewrite sign σ • r = ((sign σ : ℤ) : ℝ) * r (Units.smul_def, zsmul_eq_mul) and use contDiff_const.mul. By step 1, T ↦ T.det is C^∞, in particular C¹ and differentiable at every T; so HasFDerivAt det (fderiv ℝ det T) T for all T.
3. (Factorization at a unit.) Let T be a unit, H ∈ L(ℝⁿ), K := Ring.inverse T ∘L H. Since T ∘L Ring.inverse T = 1 (Ring.mul_inverse_cancel), for every t ∈ ℝ: T + t • H = T ∘L (1 + t • K). By multiplicativity of the determinant (LinearMap.det_comp), det(T + t • H) = det T · det(1 + t • K).
4. (Second-order expansion.) [1 + t • K] = 1 + t • [K] (LinearMap.toMatrix_one, linearity of toMatrix), so by step 1 and Matrix.det_one_add_smul, det(1 + t • K) = Matrix.det(1 + t • [K]) = 1 + Matrix.trace [K] · t + p(t) · t², where p(t) := ((Matrix.det (1 + (X : ℝ[X]) • [K].map C)).divX.divX).eval t is a polynomial function of t. Moreover Matrix.trace [K] = trace K (LinearMap.trace_eq_matrix_trace).
5. (Derivative along the line.) Put φ(t) := det(T + t • H) = det T · (1 + trace K · t + p(t) t²) (steps 3–4). The polynomial function t ↦ p(t) t² has derivative p′(t) t² + 2 t p(t), which is 0 at t = 0; hence φ has derivative det T · trace K at t = 0.
6. (Identification with the Fréchet derivative.) The curve γ(t) := T + t • H has derivative H at t = 0 and γ(0) = T; since det is differentiable at T (step 2), the chain rule (HasFDerivAt.comp_hasDerivAt) gives that φ = det ∘ γ has derivative fderiv ℝ det T H at t = 0. By uniqueness of derivatives (HasDerivAt.unique) and step 5, fderiv ℝ (fun T ↦ T.det) T H = T.det * trace(Ring.inverse T ∘L H), the second conjunct. (For n = 0, L(ℝ⁰) is the zero ring, det ≡ 1 and every trace vanishes; the argument covers this case.) ∎

## Key steps

1. det T = Matrix.det [T] = Σ_σ sign σ Π_i [T](σ i, i), a polynomial in continuous linear coordinates of T, so det is C^∞ (hence C¹).
2. At a unit T: T + tH = T ∘ (1 + tK), K = T⁻¹H, so det(T + tH) = det T · det(1 + tK).
3. Matrix.det_one_add_smul: det(1 + tK) = 1 + t trace K + p(t) t², so d/dt|₀ det(T + tH) = det T · trace K.
4. Chain rule along t ↦ T + tH and uniqueness of derivatives: fderiv det T H = det T · trace(T⁻¹ ∘ H).

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean (lines 79-120: tangentSpace, tangentProjection, normalPart, tangentFrame, tangentialDivergence, secondFundamentalForm, meanCurvature)`
- `cat -n simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,Area,SubmanifoldCalculus,SecondFundamentalFormCalculus,SecondFundamentalForm}.lean`
- `grep -rn 'contDiffAt_ringInverse\|hasFDerivAt_ringInverse\|contDiffAt_map_inverse' mathlib/Mathlib`
- `grep -rln Jacobi mathlib/Mathlib; grep -rn 'hasFDerivAt_det\|fderiv_det\|hasStrictFDerivAt_det\|deriv_det\|contDiff_det' mathlib/Mathlib (no derivative of det)`
- `grep -rn 'continuous_det\|det_one_add_smul\|derivative_det_one_add_X_smul' mathlib/Mathlib`
- `grep -rn 'theorem fderiv_fun_smul\|theorem fderiv_comp\|trace_smulRight\|theorem trace_comp_comm'\|inner_starProjection_left_eq_right\|trace_eq_sum_inner' mathlib/Mathlib`
- `grep -rn 'ContDiffAt.isSymmSndFDerivAt\|ContDiffOn.fderiv_of_isOpen\|ContDiffOn.clm_comp\|ContDiffOn.clm_apply\|fderiv_clm_apply\|fderiv_clm_comp\|adjoint_inner_left\|starProjection_apply_mem\|sub_starProjection_mem_orthogonal\|ContDiffAt.sqrt\|isUnit_iff_ker_eq_bot\|toContinuousLinearEquivOfDetNeZero\|norm_image_sub_le_of_norm_deriv_le_segment'' mathlib/Mathlib`
- `grep -rn 'theorem.*[Ss]ymm.*fderiv\|IsSymmSndFDerivAt\|iteratedFDeriv.*comm' mathlib/Mathlib (only FDeriv/Symmetric.lean, VectorField.lean, CurveIntegral/Poincare.lean)`
- `lake env lean Probe.lean / Probe2.lean: #check of every cited name after `import GMT.Ch02.Submission` (unknown: ContDiffAt.isSymmSndFDerivAt, second_derivative_symmetric_of_eventually, Chapter02.submanifoldDivergenceAt_eq_sum_inner, Convex.taylor_approx_two_segment; all others resolve)`
- `sed -n 60,115p /runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py (check_source_delta); grep leaf_lean_agent_review .humanize/swarm-configs/*.json`
- `python3 -I collision check of the 8 lean_names against dag.json (149 nodes) + grep over the run directory, snapshot project, SimonGMT and Mathlib (no match); python3 -I regex scan of dag.json lean_statements for D²ψ symmetry / det derivative (no node)`
- `python3 -I gen.py (lean_contract.validate_lean_statement + gmt-compare.contract_scope replay); lake build GMT.Ch02.Submission; lake env lean challenges8/NodeChallenge_00..07.lean`
- `lake env lean AssemblyCheck8.lean (frozen parent type from 8 child stubs + frozen sff_chart stub; #print axioms HumanizeNodeComparator.target)`
- `lake env lean Child4.lean, rev/Child15.lean, rev/Child2.lean, rev/Child3.lean, rev/Child6.lean (sibling-interface proofs, no sorry); lake env lean InstCheck.lean`
- `python3 -I numcheck.py; python3 -I numcheck2.py (finite-difference checks)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalFormCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1/parent-supplied-natural-proof.md`
- `/tmp/chartdiv-decomp/AssemblyCheck8.lean`
- `/tmp/chartdiv-decomp/InstCheck.lean`
- `/tmp/chartdiv-probe/Probe.lean`
- `/tmp/chartdiv-probe/Probe2.lean`
- `/tmp/chartdiv-probe/Child4.lean`
- `/tmp/chartdiv-probe/rev/Child15.lean`
- `/tmp/chartdiv-probe/rev/Child2.lean`
- `/tmp/chartdiv-probe/rev/Child3.lean`
- `/tmp/chartdiv-probe/rev/Child6.lean`
- `/tmp/chartdiv-scripts/numcheck.py`
- `/tmp/chartdiv-scripts/numcheck2.py`

Contract.lean (lines 83-119) fixes tangentSpace/tangentProjection (starProjection)/normalPart/tangentFrame (stdOrthonormalBasis)/tangentialDivergence (frame sum of fderiv)/secondFundamentalForm (fderivWithin of tangentProjection)/meanCurvature (frame trace). In scope after `import GMT.Ch02.Submission`: SimonGMT Area.lean (areaJacobianAt_eq_normDet, areaJacobianAt_eq_sqrt_det_adjoint_comp, areaJacobianAt_sq_eq_det_adjoint_comp, areaJacobianAt_nonneg) and Submanifold.lean (IsSimonLocalRepresentation accessors); Mathlib LinearMap.normDet_ne_zero_tfae (1-based TFAE indices), contDiffAt_ringInverse, ContDiffOn.fderiv_of_isOpen/clm_comp/clm_apply, fderiv_clm_apply/fderiv_clm_comp, fderiv_fun_smul, LinearMap.trace_smulRight/trace_comp_comm'/trace_eq_sum_inner/trace_eq_matrix_trace, Matrix.det_one_add_smul, Matrix.det_apply, LinearMap.det_toMatrix, ContDiffAt.sqrt, HasFDerivAt.sqrt, norm_image_sub_le_of_norm_deriv_le_segment', ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero, Submodule.eq_starProjection_of_mem_of_inner_eq_zero. NOT in scope (no match): ContDiffAt.isSymmSndFDerivAt, second_derivative_symmetric_of_eventually, Convex.taylor_approx_two_segment (FDeriv/Symmetric.lean is not imported) and SimonGMT submanifoldDivergenceAt_eq_sum_inner (SubmanifoldCalculus.lean is not imported) — the parent handoff's claim that these are available is wrong after the frozen imports. Mathlib has no derivative of det (no hasFDerivAt_det/fderiv_det/contDiff_det). Since a childless node may only append one theorem (leaf_verification.check_source_delta), symmetry of D²ψ and Jacobi's formula for det are genuine new obligations and became children. All 8 statements validate and elaborate; AssemblyCheck8.lean proves the frozen parent type from them plus the frozen sff_chart type (axioms propext, sorryAx from stubs, Classical.choice, Quot.sound); every sibling interface compiles sorry-free; the 8 names are unused in dag.json, the run, the snapshot project, SimonGMT and Mathlib.
