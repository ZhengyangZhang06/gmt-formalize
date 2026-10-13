# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.slice_support-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.slice_support-a1.boundary_inside-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 5 of the parent proof of cmcs_slice_support, with the set {f < t} replaced by an arbitrary set S and η₋ replaced by an arbitrary θ ∈ 𝒟^k(U) with tsupport θ̂ ⊆ S. For a form θ write θ̂ for its underlying map ℝ^P → Λ^k(ℝ^P).
0. (Boundary.) Write dθ := exteriorDerivativeTestOn U k θ ∈ 𝒟^{k+1}(U); its underlying form is exteriorDerivative θ̂. By GeometricCurrentOn.boundary_apply (a definitional equality), ∂A(θ) = A(dθ) and ∂T(θ) = T(dθ).
1. (Vanishing off S.) Let x ∉ S.
   (a) Since tsupport θ̂ ⊆ S, x ∉ tsupport θ̂, so θ̂(x) = 0 (image_eq_zero_of_notMem_tsupport).
   (b) Since tsupport(exteriorDerivative θ̂) ⊆ tsupport θ̂ (SimonGMT tsupport_exteriorDerivative_subset), also x ∉ tsupport(exteriorDerivative θ̂), so (exteriorDerivative θ̂)(x) = 0.
   (c) ξ(x) and ξ'(x) are linear maps. Hence ξ(x)((exteriorDerivative θ̂)(x)) = ξ(x)(0) = 0 and ξ'(x)(θ̂(x)) = ξ'(x)(0) = 0.
2. (Integrals over S equal integrals over ℝ^P.) Let ν be any measure and G : ℝ^P → ℝ any function with G(x) = 0 for every x ∉ S. Then ∫_S G dν = ∫ G dν (Mathlib setIntegral_eq_integral_of_forall_compl_eq_zero; no integrability or measurability hypothesis is needed). By step 1 this applies to G(x) := ξ(x)((exteriorDerivative θ̂)(x)) with ν := μ, and to G(x) := ξ'(x)(θ̂(x)) with ν := μ'.
3. (Chain of equalities.) Each equality below is justified by, in order: step 0; the representation of A applied to ω := dθ; step 2; the representation of T applied to ω := dθ; step 0; the representation of ∂T applied to θ; step 2; the representation of B applied to θ.
∂A(θ) = A(dθ) = ∫_S ξ(x)((exteriorDerivative θ̂)(x)) dμ(x) = ∫ ξ(x)((exteriorDerivative θ̂)(x)) dμ(x) = T(dθ) = ∂T(θ) = ∫ ξ'(x)(θ̂(x)) dμ'(x) = ∫_S ξ'(x)(θ̂(x)) dμ'(x) = B(θ). ∎

## Key steps

1. ∂A(θ) = A(dθ) and ∂T(θ) = T(dθ), where dθ is the test form with underlying map exteriorDerivative θ̂ (boundary_apply).
2. Off S both θ̂ and exteriorDerivative θ̂ vanish, because tsupport θ̂ ⊆ S and tsupport(exteriorDerivative θ̂) ⊆ tsupport θ̂. Since ξ(x) and ξ'(x) are linear, both integrands vanish off S.
3. So both integrals over S equal the integrals over ℝ^P (setIntegral_eq_integral_of_forall_compl_eq_zero).
4. ∂A(θ) = ∫_S ξ(dθ̂) dμ = ∫ ξ(dθ̂) dμ = T(dθ) = ∂T(θ) = ∫ ξ'(θ̂) dμ' = ∫_S ξ'(θ̂) dμ' = B(θ).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (IDENTICAL)`
- `rg -n -i 'cmcs_ss|level_split|testForm_level|exists_contDiff_zero_iff_one|smul_testForm|TestFormOn.*smul|restrict.*boundary' local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `sed -n 95,150p local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `rg -n -A6 'theorem exists_contDiff_zero_iff_one_iff_of_isClosed|theorem exists_smooth_zero_one_of_isClosed' local-references/123e8435b4a2469b/mathlib/Mathlib; sed -n 780,830p .../Geometry/Manifold/PartitionOfUnity.lean`
- `rg -n -B2 -A6 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem setIntegral_eq_zero_of_forall_eq_zero' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'image_eq_zero_of_notMem_tsupport|image_eq_one_of_notMem_mulTSupport|theorem tsupport_smul_subset_right|theorem HasCompactSupport.smul_left|theorem ContDiff.smul' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean Currents.lean (testFormOnSubmodule, exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset, GeometricCurrentOn.boundary_apply)`
- `python3 -I scan of dag.json: sibling slicing statements; lean_statement/title search for 'Disjoint (tsupport', '∃ η₁', 'split', 'Urysohn', 'partition', '{x | f x = t}'; collision check for cmcs_ss_testForm_level_split, cmcs_ss_boundary_eq_of_tsupport_subset, cmcs_ss_boundary_vanish_of_disjoint`
- `git for-each-ref | xargs -n 100 sh -c 'git grep -l -E "cmcs_ss_|testForm_level_split|boundary_eq_of_tsupport_subset|boundary_vanish_of_disjoint" "$@" -- "*.lean"' (sanity check: regcomp_covector_sq_sum_orthonormalBasis gives 25 hits)`
- `git grep across all refs for 'exists_contDiff_zero_iff_one_iff_of_isClosed' and for existing '∃ η₁ η₂ … η = η₁ + η₂' split lemmas`
- `lean GMT/Scratch/cmcs_slice_support_decomposition/{Assembly,Children,Full}.lean with #print axioms and pp.explicit check of η = η₁ + η₂`
- `sed -n 1330,1400p book/chapter-06.txt (Simon 4.6–4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-slice-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_slice_support_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_slice_support_decomposition/Children.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_slice_support_decomposition/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`

Snapshot and reuse:
- The snapshot (project b4d606db, Mathlib 25730c7c) has a Ch07 contract byte-identical to the workspace Submission.lean.
- Its project files contain no slice-support or test-form-splitting proof. Ch06 has IsRestriction and IsSlice only as frozen definitions, under main_theorem := sorry.
- No DAG node and no git ref tip declares a reusable level-split or restriction-locality lemma, so nothing can be reused.
- The three new names collide with nothing: 0 hits in 644 DAG nodes and 0 in 1267 ref tips.

Lemmas found:
- Mathlib supplies every tool the child proofs cite:
  - exists_contDiff_zero_iff_one_iff_of_isClosed (PartitionOfUnity.lean:809; takes n : ℕ∞, so n := ⊤ gives C^∞);
  - setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486) and setIntegral_eq_zero_of_forall_eq_zero (:357), with no integrability hypotheses;
  - image_eq_zero_of_notMem_tsupport, tsupport_smul_subset_right, HasCompactSupport.smul_left, ContDiff.smul and closure_minimal.
- SimonGMT supplies testFormOnSubmodule, exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset and the definitional GeometricCurrentOn.boundary_apply.

Lean checks:
- Assembly.lean proves the frozen parent from the three stubs.
- Children.lean and Full.lean prove all three children. With them, cmcs_slice_support uses only [propext, Classical.choice, Quot.sound].
- `open scoped ContDiff` must not be used in child files: it turns ω into a token and breaks the frozen statements.
