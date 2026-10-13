# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.smul_test_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof of cmcs_cutoff_defect_bound: the forms g·η and g·dη are test forms in U, being smooth and vanishing wherever η, resp. dη, vanishes. Here the step is isolated for an arbitrary test form ω ∈ 𝒟ⁿ(U). This is the C^∞-multiplier property of 𝒟ⁿ(U) that Simon 4.11 (book/chapter-06.txt lines 1378–1386) uses implicitly when it evaluates T on γ∘f·dω and on d(γ∘f·ω).

Notation: ω̂ := (ω : DifferentialForm (Euclid P) n) is the underlying form of ω, and θ := (fun x => g x • ω̂ x). Let hg : ContDiff ℝ (⊤ : ℕ∞) g be the hypothesis.

1. (What membership means.) TestFormOn U n is an abbreviation for the submodule testFormOnSubmodule U n of DifferentialForm (Euclid P) n. Its carrier is {θ | IsTestForm θ ∧ tsupport θ ⊆ U}. By the SimonGMT definitions:
   - IsTestForm θ = IsSmoothForm θ ∧ HasCompactSupport θ;
   - IsSmoothForm θ = ContDiff ℝ ∞ θ, where ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞). This is exactly the smoothness order of the hypothesis ContDiff ℝ (⊤ : ℕ∞) g;
   - HasCompactSupport θ = IsCompact (tsupport θ).
   Hence θ ∈ TestFormOn U n follows from (a) ContDiff ℝ (⊤ : ℕ∞) θ, (b) IsCompact (tsupport θ), and (c) tsupport θ ⊆ U, via the anonymous constructor ⟨⟨(a), (b)⟩, (c)⟩. Applied to ω itself, ω.property : IsTestForm ω̂ ∧ tsupport ω̂ ⊆ U gives three facts: ω̂ is C^∞ (ω.property.1.1), tsupport ω̂ is compact (ω.property.1.2), and tsupport ω̂ ⊆ U (ω.property.2).
2. (Smoothness, (a).) θ is the pointwise scalar product of the C^∞ real function g with the C^∞ map ω̂. The map ω̂ takes values in the normed space Covector (Euclid P) n of continuous alternating maps. Scalar multiplication ℝ × Covector (Euclid P) n → Covector (Euclid P) n is continuous and bilinear, so θ is C^∞. In Mathlib this is ContDiff.smul applied to hg and ω.property.1.1.
3. (Support inclusion.) If ω̂ x = 0, then θ x = g x • 0 = 0. So support θ ⊆ support ω̂, and taking closures gives tsupport θ ⊆ tsupport ω̂ (Mathlib: tsupport_smul_subset_right (fun x => g x) ω̂).
4. (Compactness, (b).) tsupport θ is closed (isClosed_tsupport θ). By step 3 it is contained in the compact set tsupport ω̂. A closed subset of a compact set is compact (IsCompact.of_isClosed_subset), so tsupport θ is compact. Implementation note: prove (b) exactly this way. Applying HasCompactSupport.smul_left to a goal written as HasCompactSupport (fun x => g x • ω̂ x) hit a whnf heartbeat timeout in testing.
5. (Support in U, (c).) By step 3 and step 1, tsupport θ ⊆ tsupport ω̂ ⊆ U.
6. (Conclusion.) Steps 2, 4 and 5 give (a), (b) and (c), so θ ∈ TestFormOn U n by step 1. ∎

## Key steps

1. Membership in TestFormOn U n unfolds to (ContDiff ℝ ∞ θ ∧ IsCompact (tsupport θ)) ∧ tsupport θ ⊆ U; ω.property gives the three facts for ω̂.
2. θ = g·ω̂ is C^∞ by ContDiff.smul.
3. tsupport θ ⊆ tsupport ω̂ by tsupport_smul_subset_right.
4. tsupport θ is a closed subset of the compact set tsupport ω̂, hence compact (IsCompact.of_isClosed_subset), and tsupport θ ⊆ tsupport ω̂ ⊆ U.

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
