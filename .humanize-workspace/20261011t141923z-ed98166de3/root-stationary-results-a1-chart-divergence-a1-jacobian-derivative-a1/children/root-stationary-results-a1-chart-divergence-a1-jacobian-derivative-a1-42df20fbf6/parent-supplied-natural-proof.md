# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.chart_divergence-a1.jacobian_derivative-a1`
- Child DAG node: `root.stationary_results-a1.chart_divergence-a1.jacobian_derivative-a1.gram_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- ℝᵈ := EuclideanSpace ℝ (Fin d) = Rn d.
- L(E, F) := E →L[ℝ] F with the operator norm, and L(ℝⁿ) := L(ℝⁿ, ℝⁿ).
- For L ∈ L(ℝⁿ, ℝᴺ), L* := ContinuousLinearMap.adjoint L ∈ L(ℝᴺ, ℝⁿ). Composition ∘ is ∘L.
- A := fderiv ℝ ψ : ℝⁿ → L(ℝⁿ, ℝᴺ), and G(x) := A(x)* ∘L A(x) ∈ L(ℝⁿ). So G is the function `fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x` of the statement.
- For x ∈ V: A'(x) := fderiv ℝ (fderiv ℝ ψ) x ∈ L(ℝⁿ, L(ℝⁿ, ℝᴺ)), and S_v := A'(x) v = D²ψ(x)[v].
No injectivity of A(x) is used. Every lemma cited resolves after `import GMT.Ch02.Submission`.
Source: parent proof, step 3 (regularity and derivative of G).

1. (The adjoint over ℝ is a continuous ℝ-linear map.) ContinuousLinearMap.adjoint is a conjugate-linear isometric equivalence L(ℝⁿ, ℝᴺ) ≃ₗᵢ⋆[ℝ] L(ℝᴺ, ℝⁿ). Over ℝ the conjugation starRingEnd ℝ is the identity ring homomorphism. Hence adjR := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Rn N)).toContinuousLinearEquiv.toContinuousLinearMap is a continuous ℝ-linear map L(ℝⁿ, ℝᴺ) →L[ℝ] L(ℝᴺ, ℝⁿ); it elaborates at this type. Moreover adjR L = L* for every L, by unfolding definitions (rfl). Being continuous linear, adjR is C^∞ (ContinuousLinearMap.contDiff). It is also its own derivative at every point: HasFDerivAt adjR adjR L (ContinuousLinearMap.hasFDerivAt).

2. (A is C¹ on V and differentiable at each x ∈ V.) ψ is C² on the open set V and 1 + 1 ≤ 2, so A = fderiv ℝ ψ is C¹ on V (ContDiffOn.fderiv_of_isOpen). Since 1 ≠ 0, A is differentiable on V (ContDiffOn.differentiableOn). For x ∈ V, V ∈ 𝓝 x because V is open (IsOpen.mem_nhds). So A is differentiable at x (DifferentiableOn.differentiableAt), that is, HasFDerivAt A (A'(x)) x (DifferentiableAt.hasFDerivAt).

3. (x ↦ A(x)* is C¹ on V, with derivative v ↦ S_v* at each x ∈ V.) By step 1, x ↦ A(x)* is definitionally the composite adjR ∘ A. The composite of the C^∞ map adjR with the map A, which is C¹ on V, is C¹ on V (ContDiff.comp_contDiffOn). For x ∈ V, apply the chain rule HasFDerivAt.comp to HasFDerivAt adjR adjR (A x) and step 2. This gives HasFDerivAt (x ↦ A(x)*) (adjR ∘L A'(x)) x. For every v, (adjR ∘L A'(x)) v = adjR (S_v) = S_v*.

4. (First conjunct.) Composition L(ℝᴺ, ℝⁿ) × L(ℝⁿ, ℝᴺ) → L(ℝⁿ), (B, C) ↦ B ∘L C, is continuous bilinear. Apply ContDiffOn.clm_comp to x ↦ A(x)* (C¹ on V by step 3) and x ↦ A(x) (C¹ on V by step 2). This shows that G = fun x ↦ A(x)* ∘L A(x) is C¹ on V.

5. (Second conjunct: product rule.) Fix x ∈ V and v ∈ ℝⁿ.
   (a) Apply HasFDerivAt.clm_comp with c := (x ↦ A(x)*), c' := adjR ∘L A'(x) (step 3), d := A and d' := A'(x) (step 2). This gives HasFDerivAt G G'_x x, where G'_x := (ContinuousLinearMap.compL ℝ ℝⁿ ℝᴺ ℝⁿ)(A(x)*) ∘L A'(x) + (ContinuousLinearMap.compL ℝ ℝⁿ ℝᴺ ℝⁿ).flip(A(x)) ∘L (adjR ∘L A'(x)).
   (b) By uniqueness of the derivative (HasFDerivAt.fderiv), fderiv ℝ G x = G'_x.
   (c) Evaluate at v using add_apply, comp_apply, compL_apply and flip_apply: fderiv ℝ G x v = A(x)* ∘L (A'(x) v) + adjR (A'(x) v) ∘L A(x) = A(x)* ∘L S_v + S_v* ∘L A(x). The last equality is adjR L = L*. It holds definitionally, so in Lean the goal closes by rfl once it is rewritten with the HasFDerivAt.fderiv equation.
   (d) This is exactly fderiv ℝ (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) x v = ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x v + ContinuousLinearMap.adjoint (fderiv ℝ (fderiv ℝ ψ) x v) ∘L fderiv ℝ ψ x.

Steps 4 and 5 are the two conjuncts. ∎

## Key steps

1. adjR := the adjoint over ℝ as a continuous ℝ-linear map L(ℝⁿ,ℝᴺ) →L[ℝ] L(ℝᴺ,ℝⁿ); adjR L = L* by rfl; adjR is C^∞ and is its own derivative.
2. A = fderiv ℝ ψ is C¹ on the open V (ContDiffOn.fderiv_of_isOpen, 1+1 ≤ 2), so HasFDerivAt A (fderiv ℝ (fderiv ℝ ψ) x) x for x ∈ V.
3. x ↦ A(x)* = adjR ∘ A is C¹ on V (ContDiff.comp_contDiffOn), with derivative adjR ∘L A'(x) at x (HasFDerivAt.comp).
4. ContDiffOn.clm_comp: G = fun x ↦ A(x)* ∘L A(x) is C¹ on V (first conjunct).
5. HasFDerivAt.clm_comp + HasFDerivAt.fderiv, evaluated at v: DG(x)[v] = A(x)* ∘L S_v + S_v* ∘L A(x) (closes by rfl; second conjunct).

## Reference use

### local-project

Queries:
- `grep -rn adjoint mathlib/Mathlib/Analysis/Calculus/ (no match)`
- `grep -rn 'HasFDerivAt.*adjoint\|adjoint.*HasFDerivAt\|contDiff.*adjoint\|adjoint.*contDiff' mathlib/Mathlib (no match)`
- `grep -rn 'trace_adjoint\|trace_comp_adjoint\|adjoint_trace' mathlib/Mathlib (no match)`
- `grep -rn trace_eq_sum_inner mathlib/Mathlib; grep -rn "theorem trace_comp_comm'" mathlib/Mathlib`
- `grep -n '^def adjoint\|^theorem adjoint_inner_left\|^theorem adjoint_inner_right' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `grep -rn 'theorem HasFDerivAt.clm_comp\|theorem ContDiffOn.clm_comp\|theorem ContDiffOn.fderiv_of_isOpen\|theorem HasFDerivAt.sqrt\|theorem ContDiffOn.sqrt\|theorem ContDiffAt.sqrt\|theorem ContinuousLinearMap.contDiff\|protected theorem hasFDerivAt' mathlib/Mathlib`
- `grep -rn 'areaJacobianAt_eq_sqrt_det_adjoint_comp\|areaJacobianAt_sq_eq_det_adjoint_comp\|areaJacobianAt_nonneg\|areaJacobianAt_eq_normDet\|def areaJacobianAt' simongmt/Poincare/SimonGMT/Chapter02/*.lean`
- `grep -rn 'theorem normDet_ne_zero_tfae' mathlib/Mathlib`
- `git -C lake-packages-25730c7c/mathlib rev-parse HEAD; diff -q snapshot vs package FDeriv/CompCLM.lean, InnerProductSpace/Trace.lean, InnerProductSpace/Adjoint.lean (identical)`
- `lake env lean probe/Probe1.lean, probe/Probe2.lean (#check of every cited name after `import GMT.Ch02.Submission`; adjR L = adjoint L by rfl)`
- `lake env lean probe/Child1.lean, probe/Child2.lean (both child proofs, sorry-free)`
- `lake env lean probe/Assembly.lean (frozen parent type from the 2 children + frozen gram_projection/det_jacobi stubs)`
- `python3 -I gen.py (flow lean_contract.validate_lean_statement + gmt-compare.child_modules contract scope); lake env lean challenges/NodeChallenge_{0,1,2}.lean`
- `lake build GMT.Ch02.Submission in /tmp/jacderiv-cand; lake env lean Sol_{0,1,2}.lean with #print axioms HumanizeNodeComparator.target`
- `python3 -I leafcheck.py (leaf_verification forbidden-token scan of each appended child proof)`
- `python3 -I dag.json lean_name/substring collision check; grep -rn of both names over the run directory, snapshot project, SimonGMT and Mathlib (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-jacobian-derivative-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-det-jacobi-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1/speculative-prompt-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/parent_verification.py`
- `/tmp/jacderiv-decomp/probe/Probe1.lean`
- `/tmp/jacderiv-decomp/probe/Probe2.lean`
- `/tmp/jacderiv-decomp/probe/Child1.lean`
- `/tmp/jacderiv-decomp/probe/Child2.lean`
- `/tmp/jacderiv-decomp/probe/Assembly.lean`
- `/tmp/jacderiv-decomp/challenges/NodeChallenge_0.lean`
- `/tmp/jacderiv-decomp/challenges/NodeChallenge_1.lean`
- `/tmp/jacderiv-decomp/challenges/NodeChallenge_2.lean`
- `/tmp/jacderiv-cand/GMT/Ch02/Submission.lean`
- `/tmp/jacderiv-cand/Sol_0.lean`
- `/tmp/jacderiv-cand/Sol_1.lean`
- `/tmp/jacderiv-cand/Sol_2.lean`
- `/tmp/jacderiv-scripts/gen.py`
- `/tmp/jacderiv-scripts/children.json`
- `/tmp/jacderiv-scripts/insert.lean`
- `/tmp/jacderiv-scripts/leafcheck.py`

Snapshot (project 1b1689a8, mathlib 25730c7c; package sources byte-identical) findings:
- Mathlib has no calculus lemma for ContinuousLinearMap.adjoint (no match under Analysis/Calculus) and no trace-of-adjoint or trace-swap lemma. These two facts (parent steps 3 and 5) are genuine new obligations, so they became the two children.
- Everything else the proofs need resolves after `import GMT.Ch02.Submission`.
  - Mathlib: ContDiffOn.fderiv_of_isOpen, ContDiffOn.clm_comp, HasFDerivAt.clm_comp, ContinuousLinearMap.contDiff/hasFDerivAt, ContDiff.comp_contDiffOn, HasFDerivAt.sqrt, ContDiffOn.sqrt, LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), LinearMap.trace_comp_comm' (LinearAlgebra/Trace.lean:265), adjoint_inner_left/right (Adjoint.lean:121/125), LinearMap.normDet_ne_zero_tfae (NormDet.lean:138, 1-based indices).
  - SimonGMT Area.lean: areaJacobianAt_eq_normDet/nonneg/sq_eq_det_adjoint_comp/eq_sqrt_det_adjoint_comp.
- The ℝ-linear adjoint (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap elaborates at type L(ℝⁿ,ℝᴺ) →L[ℝ] L(ℝᴺ,ℝⁿ) and agrees with adjoint by rfl.

Lean checks:
- Both child statements pass validate_lean_statement and elaborate as contract-scope NodeChallenge files.
- Both child proofs compile sorry-free with axioms [propext, Classical.choice, Quot.sound], and pass the leaf forbidden-token scan.
- The exact frozen parent type compiles from the two children plus the frozen sibling-type stubs; sorryAx enters only through those stubs.
- Both names are unused in dag.json, the run directory, the snapshot project, SimonGMT and Mathlib.
