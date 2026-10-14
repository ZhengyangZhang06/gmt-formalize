# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.defect_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 4.11 (book/chapter-06.txt lines 1378–1386): ∂(T⌞γ∘f)(ω) − (∂T)⌞γ∘f(ω) = T(γ∘f dω) − T(d(γ∘f ω)) = −T(γ'(f) df ∧ ω). The same identity is proved here with two changes: an arbitrary C^∞ function g replaces γ∘f, and T and ∂T are written through their integral representations. These are steps 1–3 of the parent proof of cmcs_cutoff_defect_bound.

Sibling lemmas used:
- cmcs_cd_extDeriv_smul_leibniz: for all P, k, g : Euclid P → ℝ, η : DifferentialForm (Euclid P) k and x such that g and η are differentiable at x, exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x)).
- cmcs_cd_smul_mem_testFormOn: for all P, n, U, g and ω : TestFormOn U n with ContDiff ℝ (⊤ : ℕ∞) g, (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n.

No integrability is used. Every equality of integrals below comes from one of two sources:
- a pointwise equality of integrands, via integral_congr_ae, which holds for arbitrary functions;
- one of the representation hypotheses.

Notation:
- η̂ := (η : DifferentialForm (Euclid P) k) and dη̂ := exteriorDerivative η̂;
- D(x) := ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η̂ x)), a (k+1)-covector;
- hT and hbT are the representation hypotheses of T and of T.boundary, and hg is the smoothness of g.

1. (Test forms.) Define:
   - dη := exteriorDerivativeTestOn U k η ∈ TestFormOn U (k+1). By definition of exteriorDerivativeTestOn, its underlying form is dη̂.
   - η_g := ⟨fun x => g x • η̂ x, cmcs_cd_smul_mem_testFormOn P k U g η hg⟩ ∈ TestFormOn U k.
   - ω_g := ⟨fun x => g x • (dη : DifferentialForm (Euclid P) (k+1)) x, cmcs_cd_smul_mem_testFormOn P (k+1) U g dη hg⟩ ∈ TestFormOn U (k+1). Its underlying form is x ↦ g x • dη̂ x.
   - dη_g := exteriorDerivativeTestOn U k η_g ∈ TestFormOn U (k+1). Its underlying form is exteriorDerivative (fun y => g y • η̂ y).
   - D_T := dη_g − ω_g ∈ TestFormOn U (k+1), a difference in the submodule. Its underlying form is the pointwise difference of the two underlying forms.
2. (The first integral is T ω_g.) For each x, ξ x is ℝ-linear, so ξ x (g x • dη̂ x) = g x * ξ x (dη̂ x) (map_smul, smul_eq_mul). Hence the integrands x ↦ g x * ξ x (dη̂ x) and x ↦ ξ x ((ω_g : DifferentialForm (Euclid P) (k+1)) x) agree at every x. By integral_congr_ae and hT ω_g:
   ∫ g x * ξ x (dη̂ x) dμ = ∫ ξ x (ω_g x) dμ = T ω_g.
3. (The second integral is T dη_g.) Likewise ξ' x (g x • η̂ x) = g x * ξ' x (η̂ x) for every x. By integral_congr_ae and hbT η_g:
   ∫ g x * ξ' x (η̂ x) dμ' = ∫ ξ' x (η_g x) dμ' = T.boundary η_g = T dη_g.
   The last equality is GeometricCurrentOn.boundary_apply: T.boundary θ = T (exteriorDerivativeTestOn U k θ), which holds by rfl.
4. (Pointwise value of D_T.) Fix x.
   - g is differentiable at x because it is C^∞: hg.differentiable, with the side condition 1 ≤ ∞ closed by simp.
   - η̂ is differentiable at x because it is C^∞: η.property.1.1.differentiable, with the same side condition.
   - By cmcs_cd_extDeriv_smul_leibniz P k g η̂ x, exteriorDerivative (fun y => g y • η̂ y) x = g x • dη̂ x + D(x).
   Hence the underlying form of D_T at x is
   D_T(x) = exteriorDerivative (fun y => g y • η̂ y) x − g x • dη̂ x = D(x).
   In Lean, `change` the goal to this difference, rewrite with the Leibniz lemma, and close it with `abel`.
5. (Linearity of T.) T acts through the ℝ-linear map T.toCurrent : TestFormOn U (k+1) →ₗ[ℝ] ℝ. So T D_T = T(dη_g − ω_g) = T dη_g − T ω_g, that is, T ω_g − T dη_g = −T D_T. Implementation note: after `change` to T.toCurrent, use `LinearMap.map_sub (T.toCurrent : ↥(TestFormOn U (k + 1)) →ₗ[ℝ] ℝ) (exteriorDerivativeTestOn U k η_g) ω_g` and finish with `ring`. A bare `rw [map_sub]` or `simp only [map_sub]` failed to match in testing.
6. (T D_T as an integral.) By hT D_T, T D_T = ∫ ξ x (D_T x) dμ. By step 4 (via congrArg (ξ x)) and integral_congr_ae, this equals ∫ ξ x (D(x)) dμ.
7. (Conclusion.) Steps 2, 3, 5 and 6 give
   ∫ g x * ξ x (dη̂ x) dμ − ∫ g x * ξ' x (η̂ x) dμ' = T ω_g − T dη_g = −T D_T = −∫ ξ x (D(x)) dμ,
   which is the claim. ∎

## Key steps

1. Build η_g = gη ∈ 𝒟^k(U) and ω_g = g dη ∈ 𝒟^{k+1}(U) with cmcs_cd_smul_mem_testFormOn; set dη_g := exteriorDerivativeTestOn U k η_g and D_T := dη_g − ω_g.
2. Linearity of ξ(x) and ξ'(x), integral_congr_ae and the two representations give ∫ g ξ(dη) dμ = T(ω_g) and ∫ g ξ'(η) dμ' = ∂T(η_g) = T(dη_g).
3. By cmcs_cd_extDeriv_smul_leibniz, D_T(x) = d(gη)(x) − g(x)dη(x) = alternatizeUncurryFin((Dg(x)).smulRight(η(x))) for every x.
4. Linearity of T (LinearMap.map_sub on T.toCurrent) gives T(ω_g) − T(dη_g) = −T(D_T); by the representation of T and step 3 this is −∫ ξ(D) dμ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `cmp GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (identical)`
- `rg -n 'theorem fderiv_fun_smul\b|theorem fderiv_smul\b' mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `rg -n 'theorem alternatizeUncurryFin_add|theorem alternatizeUncurryFin_smul|def alternatizeUncurryFin\b' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `rg -n 'def extDeriv\b|theorem extDeriv_smul|theorem extDeriv_fun_smul|theorem extDeriv_add|extDeriv_apply' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'theorem enorm_integral_le_lintegral_enorm|theorem integral_congr_ae\b' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `rg -n 'theorem enorm_eq_ofReal_abs' mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `rg -n 'theorem tsupport_smul_subset_right|theorem tsupport_smul_subset_left' mathlib/Mathlib/Topology/Algebra/Support.lean; rg -n 'theorem HasCompactSupport.smul_left\b' mathlib/Mathlib`
- `rg -n 'theorem IsCompact.of_isClosed_subset' mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `rg -n 'theorem ContDiff.smul\b' mathlib/Mathlib; rg -n 'theorem lintegral_mono_ae\b' mathlib/Mathlib`
- `rg -n -i 'leibniz|smulRight|smul_mem|fderiv_fun_smul|extDeriv_smul|alternatizeUncurryFin|cmcs_' local-references/123e8435b4a2469b/project -g '*.lean' (no match)`
- `rg -n 'def testFormOnSubmodule|abbrev TestFormOn|def IsTestForm|def IsSmoothForm|def exteriorDerivativeTestOn|theorem boundary_apply|abbrev exteriorDerivative|theorem tsupport_exteriorDerivative_subset|theorem exteriorDerivative_isTestForm' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `python3 -I scan of dag.json (680 nodes): lean_name collisions for cmcs_cd_extDeriv_smul_leibniz, cmcs_cd_smul_mem_testFormOn, cmcs_cd_defect_identity; lean_statements matching smulRight|extDeriv|exteriorDerivative (fun|∈ TestFormOn|alternatizeUncurryFin`
- `rg -l 'cmcs_cd_extDeriv_smul_leibniz|cmcs_cd_smul_mem_testFormOn|cmcs_cd_defect_identity' runs/20261011T150044Z-ba604216b4/nodes -g '*.json' -g '*.md'`
- `for r in $(git for-each-ref) (3200 refs): git grep -l -E 'cmcs_cd_' $r -- '*.lean' (no match)`
- `sed -n 1360,1402p book/chapter-06.txt (Simon 6.4.11)`
- `lean GMT/Scratch/cmcs_cutoff_defect_decomposition_a2/{StubsOnly,Full,Instances}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_cutoff_defect_decomposition_a2/StubsOnly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_cutoff_defect_decomposition_a2/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_cutoff_defect_decomposition_a2/Instances.lean`

Snapshot:
- The manifest pins project b4d606db and Mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace GMT/Ch07/Submission.lean.

No match:
- The snapshot project contains no Leibniz rule, smulRight lemma, smooth-multiplier closure or cmcs_ declaration.
- Mathlib DifferentialForm/Basic.lean defines extDeriv ω x := alternatizeUncurryFin (fderiv 𝕜 ω x) (line 72). It has only the constant-scalar extDeriv_smul and extDeriv_fun_smul (lines 124, 128), and no Leibniz rule for a function times a form.
- SimonGMT's testFormOnSubmodule (Currents.lean:100) is closed only under constants.

Found (every tool the child proofs cite):
- fderiv_fun_smul (FDeriv/Mul.lean:107);
- alternatizeUncurryFin, alternatizeUncurryFin_add and alternatizeUncurryFin_smul (Alternating/Uncurry/Fin.lean:124, 149, 160);
- ContDiff.smul (ContDiff/Operations.lean:567);
- tsupport_smul_subset_right (Topology/Algebra/Support.lean:172); HasCompactSupport.smul_left (line 455) is deliberately avoided because of a whnf timeout;
- IsCompact.of_isClosed_subset (Compactness/Compact.lean:105);
- integral_congr_ae and enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:301, 333);
- Real.enorm_eq_ofReal_abs (Normed/Group/Real.lean:110);
- lintegral_mono_ae (Lebesgue/Basic.lean:217);
- in SimonGMT: IsSmoothForm and IsTestForm (Forms.lean:42, 46), exteriorDerivative := extDeriv (Forms.lean:113), TestFormOn (Currents.lean:123), exteriorDerivativeTestOn (Currents.lean:193), GeometricCurrentOn.boundary_apply by rfl (Currents.lean:333), covectorEuclideanNorm (Mass.lean:30).

DAG and git:
- None of the three names occurs among the 680 DAG nodes or in any Lean file on the 3200 git refs. The only mentions are this node's own unapplied attempt-1 records.
- No accepted declaration has an identical type. dgcr_bwd_extDeriv_smul_const (constant covector) and regcomp_boundary_smul_estimate (different statement) are not reusable.

Lean (scratch _a2):
- All three child types elaborate in the contract namespace and opens, with the intended instances.
- StubsOnly.lean proves the frozen parent from the child stubs and the cmcs_wedge_norm_le stub.
- Full.lean proves every child using only propext, Classical.choice and Quot.sound.
