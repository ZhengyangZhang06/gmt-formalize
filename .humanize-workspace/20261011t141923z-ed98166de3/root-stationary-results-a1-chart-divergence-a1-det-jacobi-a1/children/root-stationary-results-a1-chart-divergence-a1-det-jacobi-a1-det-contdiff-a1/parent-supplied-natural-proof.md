# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.chart_divergence-a1.det_jacobi-a1`
- Child DAG node: `root.stationary_results-a1.chart_divergence-a1.det_jacobi-a1.det_contdiff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- ℝⁿ := Rn n = EuclideanSpace ℝ (Fin n), and L(ℝⁿ) := ℝⁿ →L[ℝ] ℝⁿ with its operator-norm normed-space structure.
- For x ∈ ℝⁿ and l ∈ Fin n, x.ofLp l is the l-th coordinate of x.
- For T ∈ L(ℝⁿ), T.det = ContinuousLinearMap.det T. By definition (an abbrev) this is LinearMap.det ↑T, where ↑T = T.toLinearMap.

Source: parent proof, steps 1–2, extracted verbatim in substance. C^∞ is replaced by an arbitrary order k : WithTop ℕ∞; every lemma used below is stated for an arbitrary order, including ∞ and ω.

Fix n ∈ ℕ and k ∈ WithTop ℕ∞.

1. (Standard basis and matrix entries.)
   - Let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, and for i ∈ Fin n let e_i := EuclideanSpace.single i (1 : ℝ). Write the literal as (1 : ℝ); otherwise Lean elaborates it in ℕ.
   - Then b i = e_i (EuclideanSpace.basisFun_apply), and b.repr x l = x.ofLp l (OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr).
   - Hence for T ∈ L(ℝⁿ) the matrix [T] := LinearMap.toMatrix b b ↑T has entries [T] l i = b.repr (T (b i)) l = (T e_i).ofLp l (LinearMap.toMatrix_apply). This entry identity holds by definitional unfolding; in Lean, `congr 1` closes it.

2. (Leibniz formula.)
   - For every T ∈ L(ℝⁿ): T.det = LinearMap.det ↑T = Matrix.det [T] (LinearMap.det_toMatrix b ↑T, read right-to-left) = Σ_{σ ∈ Equiv.Perm (Fin n)} sign σ • Π_i [T] (σ i) i (Matrix.det_apply).
   - The sign σ ∈ ℤˣ acts on ℝ through its integer value: sign σ • r = ((sign σ : ℤ) : ℝ) * r (Units.smul_def, then zsmul_eq_mul).
   - Combining with step 1, for all T:
     (∗) T.det = Σ_σ ((sign σ : ℤ) : ℝ) * Π_i (T e_i).ofLp (σ i).
   - Hence the functions T ↦ T.det and T ↦ (right side of (∗)) are equal (funext).
   - In Lean: funext T; rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]; refine Finset.sum_congr rfl fun σ _ ↦ ?_; rw [Units.smul_def, zsmul_eq_mul]; congr 1.

3. (Coordinates are continuous linear.)
   - For i, l ∈ Fin n, the map c_{i,l} : L(ℝⁿ) → ℝ, T ↦ (T e_i).ofLp l, is the continuous linear functional (EuclideanSpace.proj l) ∘L (ContinuousLinearMap.apply ℝ ℝⁿ e_i).
   - ContinuousLinearMap.apply ℝ ℝⁿ e_i : L(ℝⁿ) →L[ℝ] ℝⁿ is evaluation at e_i, and EuclideanSpace.proj l : ℝⁿ →L[ℝ] ℝ is the l-th coordinate.
   - Every continuous linear map is C^k (ContinuousLinearMap.contDiff), so each c_{i,l} is C^k.

4. (Closure properties.)
   - Fix σ. The map T ↦ Π_i c_{i,σ i}(T) is a finite product of C^k functions with values in the normed commutative ring ℝ, a normed ℝ-algebra, hence C^k (contDiff_prod).
   - The constant function T ↦ ((sign σ : ℤ) : ℝ) is C^k (contDiff_const), and a product of two C^k real-valued functions is C^k (ContDiff.mul). So each summand T ↦ ((sign σ : ℤ) : ℝ) * Π_i c_{i,σ i}(T) is C^k.
   - A finite sum of C^k functions is C^k (ContDiff.sum over Finset.univ ⊆ Equiv.Perm (Fin n)). So the right side of (∗) is a C^k function of T.
   - In Lean: refine ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ ?_), then exact ((EuclideanSpace.proj (σ i)).comp (ContinuousLinearMap.apply ℝ (Rn n) (EuclideanSpace.single i (1 : ℝ)))).contDiff.

5. (Conclusion.)
   - By step 2, the function T ↦ T.det equals the C^k function of step 4. Hence ContDiff ℝ k (fun T : Rn n →L[ℝ] Rn n ↦ T.det).
   - n and k were arbitrary, which proves the statement.
   - The argument is uniform in n. For n = 0, Perm (Fin 0) consists of the identity alone, with sign 1 and empty product 1, so (∗) is the constant 1 and the conclusion holds. ∎

## Key steps

1. Standard basis b of ℝⁿ: the entry [T] (σ i) i of LinearMap.toMatrix b b ↑T is definitionally (T e_i).ofLp (σ i), with e_i = EuclideanSpace.single i (1 : ℝ).
2. Leibniz: T.det = Matrix.det [T] = Σ_σ ((sign σ : ℤ) : ℝ) * Π_i (T e_i).ofLp (σ i) (LinearMap.det_toMatrix, Matrix.det_apply, Units.smul_def, zsmul_eq_mul).
3. Each coordinate T ↦ (T e_i).ofLp l = (EuclideanSpace.proj l ∘L ContinuousLinearMap.apply ℝ ℝⁿ e_i) T is continuous linear, hence C^k (ContinuousLinearMap.contDiff).
4. contDiff_prod, contDiff_const.mul and ContDiff.sum make the Leibniz expression C^k; rewriting det by it gives ContDiff ℝ k det for every k : WithTop ℕ∞.

## Reference use

### local-project

Queries:
- `grep -rn 'det_one_add_smul\|derivative_det_one_add_X_smul\|coeff_det_one_add_X_smul_one\|eval_det_add_X_smul\|theorem eval_det\b\|lemma eval_det\b' mathlib/Mathlib (snapshot ff09f3909baeeae7)`
- `grep -rn 'hasFDerivAt_det\|fderiv_det\|hasStrictFDerivAt_det\|deriv_det\|contDiff_det\|ContDiff.*\.det\b\|det.*contDiff\|differentiable_det\|analyticAt_det\|AnalyticAt.*det\b\|Differentiable.*det\b' mathlib/Mathlib (no match)`
- `grep -rln Jacobi mathlib/Mathlib (only EllipticCurve Jacobian coordinates, MeasureTheory/Function/Jacobian*, NormNum/LegendreSymbol, TorusIntegral: no derivative of det)`
- `grep -rn 'theorem contDiff_prod\b\|theorem ContDiff.sum\|theorem ContinuousLinearMap.contDiff\|theorem contDiff_prod' mathlib/Mathlib/Analysis/Calculus/ContDiff/*.lean; sed -n 375,500p mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `sed -n 140,215p mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean; sed -n 150,175p mathlib/Mathlib/RingTheory/MatrixPolynomialAlgebra.lean; cat mathlib/Mathlib/Topology/Algebra/Module/Determinant.lean`
- `lean Probe1.lean / Probe2.lean after `import GMT.Ch02.Submission` in the frozen contract scope: #check of every lemma cited in the child proofs (all resolve; unknown: Matrix.eval_det, Basis.det_comp, Basis.det_self, ContinuousMultilinearMap.contDiff, LinearMap.toMatrix_smul/add, ContinuousLinearMap.det_one; root-level eval_det and eval_det_add_X_smul resolve)`
- `lean Inst.lean / Inst2.lean / Inst3.lean: #synth SMulCommClass ℝ (Rn n →L[ℝ] Rn n) (Rn n →L[ℝ] Rn n) and IsScalarTower (both fail), `(0:ℝ) • H = 0` by simp (no progress) vs `zero_smul ℝ H` (ok); elaborated instances of `(1 + t • K).det` (ContinuousLinearMap.one/add/instSMul/det) plus rfl checks against `ContinuousLinearMap.id ℝ (Rn n) + t • K` and `LinearMap.det ↑(1 + t • K)``
- `lean Child1.lean; lean Child2.lean (full single-theorem proofs of both children; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I gen.py (lean_contract.validate_lean_statement from verifier and flow copies, identical; gmt-compare.child_modules in contract mode) ; lean -o candout/GMT/Ch02/Submission.olean (Submission + both children + parent assembled from children) ; lean NodeChallenge_00..02_ax.lean / NodeSolution_00..02_ax.lean with #print axioms HumanizeNodeComparator.target`
- `python3 -I collision check of contDiff_rn_continuousLinearMap_det / hasDerivAt_rn_det_one_add_smul_trace against all 170 dag.json lean_names (exact and substring) + grep -rl over the run directory, the snapshot and SimonGMT (no match)`
- `python3 -I scan of dag.json lean_statements matching '\.det\b|LinearMap\.det|Matrix\.det|trace' (related variation_matrix_det_* nodes use Matrix-valued curves; no identical accepted statement to reuse)`
- `sed -n 1,140p /runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py (check_source_delta: one appended theorem per leaf; no helper declarations, set_option or sorry)`
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/{Contract,Submission}.lean against the workspace copies (identical)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/RingTheory/MatrixPolynomialAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-det-jacobi-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-det-jacobi-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-det-jacobi-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Probe1.lean`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Probe2.lean`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Inst.lean`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Inst2.lean`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Inst3.lean`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Child1.lean`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Child2.lean`
- `/tmp/detjacobi-decomp-xXLbqa/probe/Assembly.lean`
- `/tmp/detjacobi-decomp-xXLbqa/cand/GMT/Ch02/Submission.lean`
- `/tmp/detjacobi-decomp-xXLbqa/challenges/NodeChallenge_00.lean`
- `/tmp/detjacobi-decomp-xXLbqa/challenges/NodeSolution_02.lean`
- `/tmp/detjacobi-decomp-xXLbqa/scripts/gen.py`

Mathlib 25730c7c (snapshot) has no smoothness or derivative of det (no contDiff/fderiv/HasDerivAt/analytic det lemma); it supplies only the polynomial identities Matrix.det_one_add_smul, Matrix.det_one_add_X_smul and Matrix.derivative_det_one_add_X_smul (Charpoly/Coeff.lean), plus LinearMap.det_toMatrix, Matrix.det_apply, LinearMap.trace_eq_matrix_trace, Polynomial.hasDerivAt, contDiff_prod, ContDiff.sum, ContinuousLinearMap.contDiff (all orders k : WithTop ℕ∞); ContinuousLinearMap.det is an abbrev for LinearMap.det of the coercion. All resolve after `import GMT.Ch02.Submission`. Using them, both proposed children were proved sorry-free as single theorems without set_option, and the frozen parent type was proved from the two children; comparator-style challenge and solution files (gmt-compare.child_modules, contract scope) elaborate for both children and the parent, with solutions depending only on propext, Classical.choice, Quot.sound. Instance check: in `(1 + t • K).det` the operations are ContinuousLinearMap.one/add/instSMul and ContinuousLinearMap.det (rfl-verified). Quirks on L(ℝⁿ): SMulCommClass/IsScalarTower ℝ L L fail to synthesize and simp cannot rewrite (0:ℝ) • H (the term zero_smul ℝ H works). Proposed names are unused in dag.json (170 nodes), the run, the snapshot and SimonGMT; no identical accepted node exists to reuse (the variation_matrix_det_* nodes are about Matrix-valued curves).
