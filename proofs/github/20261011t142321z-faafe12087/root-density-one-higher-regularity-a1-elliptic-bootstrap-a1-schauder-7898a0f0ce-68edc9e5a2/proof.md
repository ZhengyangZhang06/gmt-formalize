# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.caccioppoli-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.caccioppoli-a1.test_function-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (the test function zeta = eta^2 (V - c)). The parent states it for U = B_{2 rho}(y) and its particular cutoff eta. Here it is stated for any open U and any C^1 compactly supported eta with tsupport(eta) contained in U. The derivative formula is also extended to every x in R^n.
Notation. For v in R^l and a linear form p on R^n, v (x) p is the linear map h -> p(h) v in L(R^n, R^l). In Lean this is (p).smulRight v, so (D eta(x)).smulRight (V(x) - c) = (V(x) - c) (x) D eta(x). DV(x) := fderiv R V x. Outside U this is Mathlib's junk value; it only enters multiplied by eta(x)^2, which is 0 there. Let zeta(x) := eta(x)^2 (V(x) - c).
1. Supports. If zeta(x) != 0, then eta(x) != 0. So support(zeta) is contained in support(eta), and taking closures, tsupport(zeta) is contained in tsupport(eta), which is contained in U. This proves tsupport(zeta) contained in U. Also tsupport(zeta) is a closed subset of the compact set tsupport(eta), so zeta has compact support.
2. C^1 on U. eta^2 is C^1 on R^n, as a product of C^1 functions. V - c is C^1 on U. So zeta = eta^2 (V - c), a product of a C^1 scalar function and a C^1 vector function, is C^1 on U.
3. C^1 off tsupport(eta). W := the complement of tsupport(eta) in R^n is open, since tsupport is closed. For x in W, x is not in support(eta), so eta(x) = 0 and zeta(x) = 0. Thus zeta agrees on W with the constant function 0, so zeta is C^1 on W.
4. Gluing. tsupport(eta) is contained in U, so U union W = R^n. A function that is C^1 on each of two open sets is C^1 on their union, because being C^1 near a point of an open set is a local property (Mathlib: contDiff_of_contDiffOn_union_of_isOpen). Hence zeta is C^1 on R^n.
5. Derivative at x in U. Since V is C^1 on the open set U and x is in U, V is differentiable at x with derivative DV(x). Also eta is differentiable at x. The product rule for eta * eta gives D(eta^2)(x) = 2 eta(x) D eta(x). The product rule for a scalar function times a vector function gives, for every h in R^n,
D zeta(x) h = eta(x)^2 DV(x) h + (2 eta(x) D eta(x) h) (V(x) - c).
The right side is [eta(x)^2 DV(x) + 2 eta(x) (V(x) - c) (x) D eta(x)](h). So D zeta(x) = eta(x)^2 DV(x) + 2 eta(x) (V(x) - c) (x) D eta(x).
6. Derivative at x not in U. Then x is not in tsupport(eta), because tsupport(eta) is contained in U. By step 1, x is also not in tsupport(zeta). A function that vanishes on a neighbourhood of x has derivative 0 at x (fderiv_of_notMem_tsupport). So D zeta(x) = 0 and D eta(x) = 0, and eta(x) = 0. The right side of the formula is 0^2 DV(x) + (2 * 0) ((V(x) - c) (x) 0) = 0, so the formula holds at x as well.
7. Conclusion. zeta is C^1 on R^n, has compact support, and has tsupport contained in U. For every x in R^n, D zeta(x) = eta(x)^2 DV(x) + (2 eta(x)) (D eta(x)).smulRight (V(x) - c). QED
Appendix (reference Lean proof, checked; not part of the mathematical argument). At Lean v4.35.0-rc3 / Mathlib 25730c7c the declaration below compiles when placed inside `namespace Submission` of GMT/Ch05/Submission.lean (that is, inside `namespace GMT.Ch05`, after `open RectifiableVarifold`, before `main_theorem`), and the comparator's generated NodeSolution (`exact Submission.dohr_eb_sch_cacc_test_function`) closes the frozen target; `#print axioms` reports only propext, Classical.choice, Quot.sound. In this scope the bare identifier `support` resolves to `RectifiableVarifold.support`, so the proof writes `Function.support`.
```lean
theorem dohr_eb_sch_cacc_test_function : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) ∧ HasCompactSupport (fun x => η x ^ 2 • (V x - c)) ∧ tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ U ∧ ∀ x, fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x = η x ^ 2 • fderiv ℝ V x + (2 * η x) • (fderiv ℝ η x).smulRight (V x - c) := by
  intro n ℓ U V η c hU hV hη hηc hηU
  have hsupp : Function.support (fun x => η x ^ 2 • (V x - c)) ⊆ Function.support η := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have htsupp : tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ tsupport η := closure_mono hsupp
  have hcs : HasCompactSupport (fun x => η x ^ 2 • (V x - c)) := hηc.mono hsupp
  have h1 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) U :=
    ((hη.pow 2).contDiffOn).smul (hV.sub contDiffOn_const)
  have h2 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
    have heq : EqOn (fun _ => (0 : Rn ℓ)) (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
      intro x hx
      have : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
    exact contDiffOn_const.congr (fun x hx => (heq hx).symm)
  have hcover : U ∪ (tsupport η)ᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ tsupport η
    · exact Or.inl (hηU hx)
    · exact Or.inr hx
  have hcd : ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) :=
    contDiff_of_contDiffOn_union_of_isOpen h1 h2 hcover hU (isClosed_tsupport η).isOpen_compl
  refine ⟨hcd, hcs, htsupp.trans hηU, fun x => ?_⟩
  by_cases hx : x ∈ U
  · have hVd : HasFDerivAt V (fderiv ℝ V x) x :=
      (((hV.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hηd : HasFDerivAt η (fderiv ℝ η x) x := ((hη.differentiable one_ne_zero) x).hasFDerivAt
    have hsq : HasFDerivAt (fun x => η x ^ 2) ((2 * η x) • fderiv ℝ η x) x := by
      have := hηd.mul hηd
      convert this using 1
      · ext y; simp [sq]
      · rw [two_mul, add_smul]
    have hprod := hsq.smul (hVd.sub_const c)
    rw [show (fun x => η x ^ 2 • (V x - c)) = ((fun x => η x ^ 2) • fun x => V x - c) from rfl,
      hprod.fderiv]
    ext v
    simp [ContinuousLinearMap.smulRight_apply, smul_smul, mul_comm]
  · have hx' : x ∉ tsupport η := fun h => hx (hηU h)
    have hxζ : x ∉ tsupport (fun x => η x ^ 2 • (V x - c)) := fun h => hx' (htsupp h)
    rw [fderiv_of_notMem_tsupport ℝ hxζ, fderiv_of_notMem_tsupport ℝ hx',
      image_eq_zero_of_notMem_tsupport hx']
    ext v
    simp
```

## Key steps

1. support zeta lies in support eta, so tsupport zeta lies in tsupport eta, which lies in U; hence zeta has compact support
2. zeta is C^1 on U (product of C^1 maps) and vanishes identically on the open complement of tsupport eta
3. these two open sets cover R^n, so zeta is C^1 on R^n (contDiff_of_contDiffOn_union_of_isOpen)
4. for x in U, the product rule gives D zeta = eta^2 DV + (2 eta D eta) (x) (V - c)
5. for x not in U, zeta and eta vanish near x, so both sides are 0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp workspace GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean (byte-identical)`
- `grep -rli 'caccioppoli' <snapshot>/mathlib/Mathlib (0 files); grep -rli 'caccioppoli\|energy estimate\|cutoff\|cut-off' <snapshot>/mathlib/Mathlib/Analysis <snapshot>/mathlib/Mathlib/MeasureTheory <snapshot>/project (only project/GMT/Ch05/README.md)`
- `grep -n 'theorem\|lemma' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `grep -rn 'continuous_of_tsupport\|contDiff_of_tsupport\|of_tsupport_subset\|fderiv_of_notMem_tsupport\|support_fderiv_subset\|continuous_of_mulTSupport' <snapshot>/mathlib/Mathlib`
- `grep (pinned Mathlib) for contDiff_of_contDiffOn_union_of_isOpen, HasFDerivAt.norm_sq, HasFDerivAt.mul_const, HasDerivAt.comp_hasFDerivAt, innerSL_apply_norm, norm_smulRight_apply, ContDiffOn.continuousOn_fderiv_of_isOpen, Continuous.integrable_of_hasCompactSupport, ofReal_integral_eq_lintegral_ofReal, lintegral_const_mul', setLIntegral_le_lintegral`
- `python3 scan of run dag.json (lean_name, theorems, raw text) for the proposed names and for cutoff/bump/Caccioppoli nodes`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') and child_modules(...) to generate NodeChallenge/NodeSolution files`
- `lake build GMT.Ch05.Submission; lake env lean Checks/{Elab,Assembly,Cutoff,TestFun,Energy,InstVerify,Sol_cutoff,Sol_test_function,Sol_energy_estimate,Sol_parent}.lean in scratch /tmp/cacc-decomp-zgZPXQ/proj (Lean v4.35.0-rc3, shared lake-packages-25730c7c)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean.

The pinned Mathlib has no Caccioppoli or energy-estimate result: 'caccioppoli' has 0 matches in Mathlib/, and the only cutoff/Caccioppoli hit in Analysis, MeasureTheory or the project is the chapter README. The proof is assembled from these pinned tools:
- Cutoff profile: Real.smoothTransition (SmoothTransition.lean: one_of_one_le :161, zero_of_nonpos :168, contDiff :205).
- Cutoff gradient bound: HasFDerivAt.norm_sq (InnerProductSpace/Calculus.lean:211), HasFDerivAt.mul_const (FDeriv/Mul.lean:299), HasDerivAt.comp_hasFDerivAt (Deriv/Comp.lean:171) and innerSL_apply_norm (InnerProductSpace/LinearMap.lean:225).
- Test function: contDiff_of_contDiffOn_union_of_isOpen (ContDiff/Basic.lean:612), and fderiv_of_notMem_tsupport and support_fderiv_subset (FDeriv/Const.lean:375-381).
- Energy estimate: ContinuousOn.continuous_of_tsupport_subset (to_additive of Topology/Algebra/Support.lean:196), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916), Continuous.integrable_of_hasCompactSupport (Function/LocallyIntegrable.lean:622), ContinuousLinearMap.norm_smulRight_apply (Normed/Operator/Bilinear.lean:449) and ofReal_integral_eq_lintegral_ofReal (Integral/Bochner/Basic.lean:739).
- Parent assembly: lintegral_const_mul' (Lebesgue/Add.lean:420) and setLIntegral_le_lintegral (Lebesgue/Basic.lean:258).

dag.json contains accepted cutoffs exists_smooth_cutoff_half_ball_grad_le and aal_l1th_exists_cutoff. Each equals 1 on closedBall xi (rho/2), vanishes for dist >= rho, and has gradient at most 3/rho. They are not reused: with the fixed 1/2 ratio and vanishing only on a closed set, they cannot equal 1 on the open B_rho(y) while keeping tsupport inside the open B_{2rho}(y). A new cutoff child is therefore needed. None of the three proposed names occurs in dag.json.

In the replayed scope, bare `support` is RectifiableVarifold.support, so the proofs write Function.support.

Scratch-build Lean checks:
- All child types and the frozen parent type elaborate.
- The parent follows from the cutoff and energy_estimate types.
- energy_estimate follows from the test_function type.
- cutoff and test_function are proved outright.
- All four verifier-generated NodeSolution targets close by exact Submission.X, using only propext, Classical.choice and Quot.sound.
