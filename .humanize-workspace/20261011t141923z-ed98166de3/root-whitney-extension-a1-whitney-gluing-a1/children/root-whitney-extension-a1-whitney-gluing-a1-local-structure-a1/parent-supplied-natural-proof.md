# Parent-supplied natural-language proof

- Parent DAG node: `root.whitney_extension-a1.whitney_gluing-a1`
- Child DAG node: `root.whitney_extension-a1.whitney_gluing-a1.local_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 ((1a)-(1f)) of the supplied proof of whitney_jet_gluing_c1, specialized to the hypotheses that step uses (A closed, (P2)-(P5), and the formula (G) for g off A). (P1), (P6), (P7), (W) and the continuity of ν are not needed here.

Notation. U := ℝⁿ ∖ A, open because A is closed. P_i(y) := h(p_i) + ⟨ν(p_i), y − p_i⟩. For v ∈ ℝⁿ, L_v := innerSL ℝ v, the continuous linear functional w ↦ ⟨v, w⟩ (innerSL_apply_apply). Dψ(y) := fderiv ℝ ψ y, and ‖·‖ on functionals is the operator norm.

Proof.

1. The affine pieces. For each i, P_i(y) = h(p_i) + L_{ν(p_i)}(y − p_i). The map y ↦ y − p_i has derivative id at every point, the continuous linear map L_{ν(p_i)} is its own derivative, and adding the constant h(p_i) does not change derivatives. By the chain rule, HasFDerivAt P_i L_{ν(p_i)} y for every y ∈ ℝⁿ. Likewise P_i is C¹ on ℝⁿ, being a constant plus a continuous linear map composed with a translation.

2. Choice of s. Fix x ∉ A. By (P4) choose a finite s ⊆ ι and V ∈ 𝓝 x with φ_i(y) = 0 for all i ∉ s and all y ∈ V. Since U is open and x ∈ U, U ∈ 𝓝 x, so W := V ∩ U ∈ 𝓝 x. As x ∈ V (mem_of_mem_nhds), φ_i(x) = 0 for every i ∉ s.

3. Finite sums on W. Let y ∈ W. If i ∉ s then φ_i(y) = 0 (y ∈ V), hence also φ_i(y)P_i(y) = 0. So the supports of i ↦ φ_i(y) and of i ↦ φ_i(y)P_i(y) lie in the finite set s, and each finsum equals the finite sum over s (finsum_eq_sum_of_support_subset). Since y ∈ U, (G) and (P5) give
(3a) g(y) = Σ_{i∈s} φ_i(y)P_i(y), and
(3b) Σ_{i∈s} φ_i(y) = 1.
Put G(y) := Σ_{i∈s} φ_i(y)P_i(y) and Φ(y) := Σ_{i∈s} φ_i(y). Since W ∈ 𝓝 x, g =ᶠ[𝓝 x] G and Φ =ᶠ[𝓝 x] 1.

4. g is C¹ at x. Each φ_i is C¹ at x by (P2), as x ∉ A, and each P_i is C¹ (step 1). So each product φ_i·P_i is C¹ at x (ContDiffAt.mul), and so is the finite sum G (ContDiffAt.sum). Since g =ᶠ[𝓝 x] G, g is C¹ at x (ContDiffAt.congr_of_eventuallyEq). This is the first conclusion.

5. Derivatives of the sums over s. Each φ_i is differentiable at x (C¹ at x with 1 ≠ 0), so HasFDerivAt φ_i (Dφ_i(x)) x. By the product rule (HasFDerivAt.mul) and step 1, HasFDerivAt (φ_i·P_i) (φ_i(x)•L_{ν(p_i)} + P_i(x)•Dφ_i(x)) x. By the sum rule (HasFDerivAt.fun_sum), HasFDerivAt G (Σ_{i∈s}[φ_i(x)•L_{ν(p_i)} + P_i(x)•Dφ_i(x)]) x. Since g =ᶠ[𝓝 x] G, Dg(x) = DG(x) (Filter.EventuallyEq.fderiv_eq), that is,
(5a) Dg(x) = Σ_{i∈s}(φ_i(x)•L_{ν(p_i)} + P_i(x)•Dφ_i(x)).
By the sum rule again, HasFDerivAt Φ (Σ_{i∈s} Dφ_i(x)) x. On the other hand, the constant function 1 has derivative 0 and Φ =ᶠ[𝓝 x] 1, so HasFDerivAt Φ 0 x (hasFDerivAt_const, HasFDerivAt.congr_of_eventuallyEq). By uniqueness of the Fréchet derivative (HasFDerivAt.unique),
(5b) Σ_{i∈s} Dφ_i(x) = 0.

6. Zero weights have zero derivative. Let i ∈ ι with φ_i(x) = 0. For every y ∈ U, φ_i(y) ≥ 0 = φ_i(x) by (P3). Since U ∈ 𝓝 x, x is a local minimum of φ_i, and therefore Dφ_i(x) = 0 (IsLocalMin.fderiv_eq_zero). By step 2 this applies in particular to every i ∉ s.

7. The set S. Put S := {i ∈ s : φ_i(x) ≠ 0} (Finset.filter), a finite subset of ι. For i ∈ S, φ_i(x) ≥ 0 by (P3) and φ_i(x) ≠ 0, hence φ_i(x) > 0.

8. Sums over S. For i ∈ s ∖ S we have φ_i(x) = 0 and, by step 6, Dφ_i(x) = 0. So for such i each of the summands vanishes: φ_i(x); φ_i(x)P_i(x); φ_i(x)•L_{ν(p_i)} + P_i(x)•Dφ_i(x) = 0•L_{ν(p_i)} + P_i(x)•0; and Dφ_i(x). Hence each finite sum over s of these summands equals the corresponding sum over S (Finset.sum_filter_of_ne, Finset.sum_filter_ne_zero). Apply this to (3b) and (3a) at y := x (x ∈ W), to (5a) and to (5b):
Σ_{i∈S} φ_i(x) = 1; g(x) = Σ_{i∈S} φ_i(x)P_i(x); Dg(x) = Σ_{i∈S}(φ_i(x)•L_{ν(p_i)} + P_i(x)•Dφ_i(x)); Σ_{i∈S} Dφ_i(x) = 0.

9. The finsum of the norms. Let i ∈ ι with ‖Dφ_i(x)‖ ≠ 0. Then Dφ_i(x) ≠ 0, so φ_i(x) ≠ 0 by step 6, so i ∈ s by step 2, and hence i ∈ S. The support of i ↦ ‖Dφ_i(x)‖ is therefore contained in S, and finsum_eq_sum_of_support_subset gives Σᶠ_i ‖Dφ_i(x)‖ = Σ_{i∈S} ‖Dφ_i(x)‖.

10. Steps 4, 7, 8 and 9 give every conclusion at the arbitrary point x ∉ A. ∎

Formalization remark (non-normative; the numbered proof above is complete without it). During the decomposition session the frozen type was proved verbatim by the following declaration. It was kernel-checked against a scratch build of GMT.Ch02.Submission at the frozen commit, with Lean v4.35.0-rc3 and Mathlib 25730c7c, and uses only the axioms propext, Classical.choice and Quot.sound. It follows steps 1-10 above. Placed inside `namespace GMT.Ch02` of GMT/Ch02/Submission.lean, before `main_theorem`, it elaborates unchanged:

theorem Submission.whitney_gluing_local_structure : (∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (g : Rn n → ℝ), IsClosed A → (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) → (∀ i, ∀ x ∉ A, 0 ≤ φ i x) → (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) → (∀ x ∉ A, ∑ᶠ i, φ i x = 1) → (∀ x ∉ A, g x = ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ∀ x ∉ A, ContDiffAt ℝ 1 g x ∧ ∃ S : Finset ι, (∀ i ∈ S, 0 < φ i x) ∧ ∑ i ∈ S, φ i x = 1 ∧ g x = ∑ i ∈ S, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i)) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x) ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ = ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖) := by
  intro n A h ν ι φ p g hA hφC1 hφnn hlf hsum hgU x hx
  classical
  obtain ⟨s, V, hV, hVzero⟩ := hlf x hx
  set P : ι → Rn n → ℝ := fun i y => h (p i) + inner ℝ (ν (p i)) (y - p i) with hPdef
  have hPderiv : ∀ i y, HasFDerivAt (P i) (innerSL ℝ (ν (p i))) y := by
    intro i y
    have h1 := (((innerSL ℝ (ν (p i))).hasFDerivAt (x := y - p i)).comp y
      ((hasFDerivAt_id y).sub_const (p i))).const_add (h (p i))
    simpa [P, Function.comp_def, innerSL_apply_apply] using h1
  have hPcd : ∀ i, ContDiff ℝ 1 (P i) := by
    intro i
    exact contDiff_const.add ((innerSL ℝ (ν (p i))).contDiff.comp (contDiff_id.sub contDiff_const))
  have hU : (Aᶜ : Set (Rn n)) ∈ 𝓝 x := hA.isOpen_compl.mem_nhds hx
  have hW : V ∩ Aᶜ ∈ 𝓝 x := inter_mem hV hU
  have hrep : ∀ y ∈ V ∩ Aᶜ, g y = ∑ i ∈ s, φ i y * P i y ∧ ∑ i ∈ s, φ i y = 1 := by
    intro y hy
    have hsupp1 : Function.support (fun i => φ i y) ⊆ ↑s := by
      intro i hi
      by_contra his
      exact hi (hVzero i his y hy.1)
    have hsupp2 : Function.support (fun i => φ i y * P i y) ⊆ ↑s := by
      intro i hi
      by_contra his
      apply hi
      simp [hVzero i his y hy.1]
    constructor
    · rw [hgU y hy.2, finsum_eq_sum_of_support_subset _ hsupp2]
    · rw [← finsum_eq_sum_of_support_subset _ hsupp1]
      exact hsum y hy.2
  have hg_ev : g =ᶠ[𝓝 x] fun y => ∑ i ∈ s, φ i y * P i y := by
    filter_upwards [hW] with y hy using (hrep y hy).1
  have hsum_ev : (fun y => ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hW] with y hy using (hrep y hy).2
  have hGcd : ContDiffAt ℝ 1 (fun y => ∑ i ∈ s, φ i y * P i y) x :=
    ContDiffAt.sum fun i _ => (hφC1 i x hx).mul (hPcd i).contDiffAt
  have hgcd : ContDiffAt ℝ 1 g x := hGcd.congr_of_eventuallyEq hg_ev
  have hφdiff : ∀ i, DifferentiableAt ℝ (φ i) x := fun i =>
    (hφC1 i x hx).differentiableAt (by norm_num)
  have hGderiv : HasFDerivAt (fun y => ∑ i ∈ s, φ i y * P i y)
      (∑ i ∈ s, (φ i x • innerSL ℝ (ν (p i)) + P i x • fderiv ℝ (φ i) x)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (hφdiff i).hasFDerivAt.mul (hPderiv i x)
  have hfd_s : fderiv ℝ g x = ∑ i ∈ s, (φ i x • innerSL ℝ (ν (p i)) + P i x • fderiv ℝ (φ i) x) := by
    rw [hg_ev.fderiv_eq, hGderiv.fderiv]
  have hD0_s : ∑ i ∈ s, fderiv ℝ (φ i) x = 0 := by
    have h1 : HasFDerivAt (fun y => ∑ i ∈ s, φ i y) (∑ i ∈ s, fderiv ℝ (φ i) x) x :=
      HasFDerivAt.fun_sum fun i _ => (hφdiff i).hasFDerivAt
    have h2 : HasFDerivAt (fun y => ∑ i ∈ s, φ i y) (0 : Rn n →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hsum_ev
    exact h1.unique h2
  -- indices with zero weight have zero derivative (local minimum)
  have hzero : ∀ i, φ i x = 0 → fderiv ℝ (φ i) x = 0 := by
    intro i hi
    apply IsLocalMin.fderiv_eq_zero
    filter_upwards [hU] with y hy
    rw [hi]
    exact hφnn i y hy
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hout : ∀ i, i ∉ s → φ i x = 0 := fun i hi => hVzero i hi x hxV
  let S : Finset ι := s.filter (fun i => φ i x ≠ 0)
  have hSpos : ∀ i ∈ S, 0 < φ i x := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact lt_of_le_of_ne (hφnn i x hx) (Ne.symm hi')
  have hS1 : ∑ i ∈ S, φ i x = 1 := by
    have := (hrep x ⟨hxV, hx⟩).2
    rw [← this]
    exact Finset.sum_filter_ne_zero s
  refine ⟨hgcd, S, hSpos, hS1, ?_, ?_, ?_, ?_⟩
  · rw [(hrep x ⟨hxV, hx⟩).1]
    symm
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (by rw [h0, zero_mul])
  · rw [hfd_s]
    symm
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (by rw [h0, hzero i h0, zero_smul, smul_zero, add_zero])
  · rw [← hD0_s]
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (hzero i h0)
  · apply finsum_eq_sum_of_support_subset
    intro i hi
    have hne : fderiv ℝ (φ i) x ≠ 0 := by
      intro h0
      exact hi (by simp [h0])
    have hφne : φ i x ≠ 0 := fun h0 => hne (hzero i h0)
    have his : i ∈ s := by
      by_contra his
      exact hφne (hout i his)
    exact Finset.mem_filter.mpr ⟨his, hφne⟩

## Key steps

1. P_i is affine with HasFDerivAt P_i ⟨ν(p_i),·⟩ at every point; fix x ∉ A, take s and V from (P4), and put W := V ∩ (ℝⁿ∖A) ∈ 𝓝 x.
2. On W both finsums are finite sums over s (finsum_eq_sum_of_support_subset): g = Σ_{i∈s} φ_i P_i, and Σ_{i∈s} φ_i = 1 by (P5).
3. g is C¹ at x (ContDiffAt.mul, ContDiffAt.sum, congr_of_eventuallyEq). The product and sum rules give Dg(x) as a sum over s, and uniqueness of derivatives gives Σ_{i∈s} Dφ_i(x) = 0.
4. If φ_i(x) = 0, then x is a local minimum of φ_i, which is ≥ 0 on the open set ℝⁿ∖A, so Dφ_i(x) = 0. This covers every i ∉ s.
5. With S := {i ∈ s : φ_i(x) ≠ 0}: every sum over s equals the sum over S, φ_i(x) > 0 on S, and i ↦ ‖Dφ_i(x)‖ is supported in S, so its finsum is the sum over S.

## Reference use

### local-project

Queries:
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `rg -n "Whitney|whitney" local-references/ff09f3909baeeae7/project/GMT`
- `rg -n "whitney_gluing_local_structure|whitney_gluing_hasFDerivAt|whitney_gluing_continuousAt_fderiv" <run dir> local-references/ff09f3909baeeae7/project local-references/ff09f3909baeeae7/mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare (exit 1: no match); dag.json lean_name scan for the same names (absent)`
- `rg -n "theorem IsLocalMin.fderiv_eq_zero|theorem innerSL_apply_apply|theorem innerSL_apply_norm|theorem contDiff_one_iff_fderiv|theorem ContDiffAt.continuousAt_fderiv|theorem ContDiffAt.congr_of_eventuallyEq|theorem HasFDerivAt.mul |theorem ContDiffAt.sum|theorem abs_real_inner_le_norm|theorem infDist_le_dist_of_mem|theorem IsCompact.inter_left|theorem abs_sum_le_sum_abs" mathlib/Mathlib`
- `rg -n "finsum_eq_sum_of_support_subset|theorem sum_filter_of_ne|theorem sum_filter_ne_zero|exists_infDist_eq_dist|notMem_iff_infDist_pos|HasFDerivAt.of_isLittleO|EventuallyEq.fderiv_eq" mathlib/Mathlib`
- `rg -n "theorem finsum_eq_sum_of_support_subset|theorem prod_filter_of_ne|theorem prod_filter_ne_one|theorem HasFDerivAt.sum|theorem IsLittleO.of_bound|theorem continuousWithinAt_iff|theorem continuousAt_iff|theorem HasFDerivAt.unique|theorem HasFDerivAt.congr_of_eventuallyEq|theorem hasFDerivAt_const|theorem mem_of_mem_nhds" mathlib/Mathlib`
- `full reads of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean and WhitneyExtension.lean; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 | grep -i whitney; grep import Poincare/SimonGMT.lean | grep -i whitney (exit 1)`
- `lean -R . -o /tmp/gluing-decomp/build/GMT/Ch02/Submission.olean GMT/Ch02/Submission.lean (scratch copy of the frozen Submission; LEAN_PATH = scratch build + shared package oleans, read-only)`
- `python3 -I gen.py (gmt-compare.py layout/child_modules + lean_contract.validate_lean_statement), then lean NodeChallenge_00.lean NodeChallenge_01.lean NodeChallenge_02.lean`
- `lean asm/AssemblyCheck.lean; lean c1/Child1Check.lean; lean c2/Child2Check.lean; lean c3/Child3Check.lean (each with #print axioms)`
- `lean full/GMT/Ch02/Submission.lean (copy with Submission.whitney_gluing_* and Submission.whitney_jet_gluing_c1 inserted before main_theorem), then lean full/NodeSolution_0..3.lean (exact Submission.X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Finprod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1/decomposition-v1.json`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_00.lean`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_01.lean`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_02.lean`
- `/tmp/gluing-decomp/asm/AssemblyCheck.lean`
- `/tmp/gluing-decomp/c1/Child1Check.lean`
- `/tmp/gluing-decomp/c2/Child2Check.lean`
- `/tmp/gluing-decomp/c3/Child3Check.lean`
- `/tmp/gluing-decomp/full/GMT/Ch02/Submission.lean`

Snapshot and names:
- The snapshot's project/GMT/Ch02/Contract.lean is byte-identical to the workspace contract (cmp).
- In project/GMT, 'Whitney' occurs only in the WhitneyExtension definition (Contract/Submission lines 204-208) and README rows 3-4.
- None of the three proposed names occurs anywhere: run directory, dag.json lean_name fields, snapshot project, snapshot Mathlib, or simongmt (rg exit 1). The names are unreserved.

Mathlib reuse. Snapshot Mathlib has no abstract Whitney-gluing lemma, but supplies every tool the child proofs cite:
- IsLocalMin.fderiv_eq_zero (LocalExtr/Basic.lean:181);
- finsum_eq_sum_of_support_subset (to_additive of Finprod.lean:350);
- Finset.sum_filter_of_ne / sum_filter_ne_zero (to_additive of Group/Finset/Basic.lean:319/328);
- innerSL_apply_apply and innerSL_apply_norm (InnerProductSpace/LinearMap.lean:172/225);
- abs_real_inner_le_norm (InnerProductSpace/Basic.lean:471);
- ContDiffAt.congr_of_eventuallyEq and contDiff_one_iff_fderiv (ContDiff/Defs.lean:966/1261);
- ContDiffAt.continuousAt_fderiv (ContDiff/Comp.lean:816);
- ContDiffAt.sum (ContDiff/Operations.lean:369);
- HasFDerivAt.mul (FDeriv/Mul.lean:205);
- HasFDerivAt.sum, with fun_sum generated by to_fun (FDeriv/Add.lean:418);
- HasFDerivAt.unique (FDeriv/Basic.lean:174);
- HasFDerivAt.congr_of_eventuallyEq and Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:176/260);
- hasFDerivAt_const (FDeriv/Const.lean:115);
- HasFDerivAt.of_isLittleO (FDeriv/Defs.lean:230);
- IsLittleO.of_bound (Asymptotics/Defs.lean:185);
- infDist_le_dist_of_mem, IsClosed.notMem_iff_infDist_pos and IsClosed.exists_infDist_eq_dist (HausdorffDistance.lean:500/584/615);
- Metric.continuousAt_iff and continuousWithinAt_iff (Pseudo/Defs.lean:871/875);
- IsCompact.inter_left (Compactness/Compact.lean:96);
- abs_sum_le_sum_abs (Order/BigOperators/Group/Finset.lean:371);
- mem_of_mem_nhds (Neighborhoods.lean:85).

SimonGMT. The pinned WhitneyExtension.lean proves the analogous facts for its own WhitneyBallCover:
- whitneyExtension_contDiffAt_compl and whitneyExtension_fderiv_eq_near_sum correspond to child 1;
- HasWhitneyC1Compatibility.hasFDerivAt_whitneyExtension corresponds to child 2;
- continuousAt_fderiv_whitneyExtension, with norm_fderiv_whitneyExtension_sub_le, corresponds to child 3.
WhitneyExtension has no .olean (only WhitneyCover/Jet/Partition do), and Poincare/SimonGMT.lean imports no Whitney file. So it served only as a template, and the children were proved from Mathlib alone.

Lean checks. All ran in /tmp scratch with the pinned toolchain; the shared package tree and workspace stayed untouched.
- The three types elaborate in the verifier-generated NodeChallenge modules.
- AssemblyCheck derives the selected exact type from them.
- Child1-3Check prove each exact type.
- The Submission copy compiles Submission.whitney_gluing_* and Submission.whitney_jet_gluing_c1, and NodeSolution_0..3 pass.
- #print axioms reports only propext, Classical.choice and Quot.sound everywhere.
