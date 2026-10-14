# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.weighted_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1–2 (bounded field; integrability of τ = θζ). Notation: e_1, …, e_P is the standard orthonormal basis (EuclideanSpace.basisFun). ‖·‖ denotes the operator norms on Covector (Euclid P) n (continuous alternating n-linear forms) and on MultiVector P n = (Covector (Euclid P) n →L[ℝ] ℝ). Put C := √(card(Fin n → Fin P)) = √(Pⁿ) ≥ 0.
1. Measurability. θ is a measurable real function, hence strongly measurable, and ζ is strongly measurable. So x ↦ θ(x)•ζ(x) is strongly measurable (StronglyMeasurable.smul).
2. Coefficient norm versus operator norm. Let α be an n-covector. For every I : Fin n → Fin P, |α(e_{I(1)}, …, e_{I(n)})| ≤ ‖α‖·∏_i ‖e_{I(i)}‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm; ‖e_j‖ = 1). Now covectorEuclideanNorm α = √(Σ_{I : Fin n → Fin P} [StrictMono I]·α(e_I)²), and each summand is ≤ ‖α‖²; the summands with I not strictly increasing are 0. Summing over the card(Fin n → Fin P) indices and using monotonicity of √ (Real.sqrt_le_sqrt, Real.sqrt_mul, Real.sqrt_sq) gives covectorEuclideanNorm α ≤ √(card·‖α‖²) = C·‖α‖.
3. Bounded field. For every x and α, |ζ(x)(α)| ≤ covectorEuclideanNorm α ≤ C·‖α‖. As C ≥ 0, ContinuousLinearMap.opNorm_le_bound gives ‖ζ(x)‖ ≤ C.
4. Pointwise bound on M. Let x ∈ M, so θ(x) > 0. Scalar multiplication of continuous linear maps is pointwise, (c•f)(α) = c·f(α). Hence for every α, |(θ(x)•ζ(x))(α)| = θ(x)·|ζ(x)(α)| ≤ θ(x)·C·‖α‖, and opNorm_le_bound gives ‖θ(x)•ζ(x)‖ ≤ C·θ(x). (Formalisation note: argue through opNorm_le_bound rather than norm_smul or enorm_smul, because the instances NormSMulClass ℝ (MultiVector P n) and ENormSMulClass ℝ (MultiVector P n) are not found with the default instances.) Therefore ‖θ(x)•ζ(x)‖ₑ = ofReal ‖θ(x)•ζ(x)‖ ≤ ofReal(C)·ofReal(θ(x)) (ofReal_norm; ENNReal.ofReal_mul, as C ≥ 0).
5. Integral bound. M is measurable and the bound of step 4 holds at every point of M (setLIntegral_mono'). Hence ∫⁻_M ‖θ•ζ‖ₑ dμ ≤ ∫⁻_M ofReal(C)·ofReal(θ) dμ = ofReal(C)·∫⁻_M ofReal(θ) dμ (lintegral_const_mul, since x ↦ ofReal(θ(x)) is measurable). This is < ∞ because ofReal(C) < ∞ and ∫⁻_M ofReal(θ) dμ < ∞ by hypothesis (ENNReal.mul_lt_top). Together with step 1 this is the claim. ∎

Validated Lean tactic script. It was kernel-checked during this decomposition inside a copy of GMT/Ch07/Submission.lean, at the insertion point used for child declarations, with default heartbeats; the only axioms are propext, Classical.choice and Quot.sound. It is the body after `theorem Submission.cbr_ci_gp_weighted_field_l1 : <frozen type> := by`:
```lean
  intro P n μ M θ ζ hM hθ hζ hpos hint hbound
  refine ⟨hθ.stronglyMeasurable.smul hζ, ?_⟩
  classical
  set C : ℝ := Real.sqrt ((Fintype.card (Fin n → Fin P) : ℝ)) with hC
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  -- Step 1: the Euclidean coefficient norm is dominated by `C` times the operator norm
  have hcov : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    intro α
    have hterm : ∀ I : Fin n → Fin P,
        (if StrictMono I then (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
          ≤ ‖α‖ ^ 2 := by
      intro I
      split_ifs
      · have h1 : ‖α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))‖ ≤ ‖α‖ := by
          have := α.le_opNorm (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))
          simpa using this
        have h2 : |α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ‖α‖ := by
          simpa [Real.norm_eq_abs] using h1
        nlinarith [abs_nonneg (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))),
          sq_abs (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i)))]
      · positivity
    have hsum : (∑ I : Fin n → Fin P,
        if StrictMono I then (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
          ≤ (Fintype.card (Fin n → Fin P) : ℝ) * ‖α‖ ^ 2 := by
      calc _ ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := Finset.sum_le_sum fun I _ => hterm I
        _ = _ := by simp
    unfold covectorEuclideanNorm
    calc Real.sqrt _ ≤ Real.sqrt ((Fintype.card (Fin n → Fin P) : ℝ) * ‖α‖ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = C * ‖α‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  -- Step 2: `‖ζ x‖ ≤ C`
  have hζC : ∀ x, ‖ζ x‖ ≤ C := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun α => ?_
    rw [Real.norm_eq_abs]
    exact (hbound x α).trans (hcov α)
  -- Step 3: the lintegral bound
  calc ∫⁻ x in M, ‖θ x • ζ x‖ₑ ∂μ ≤ ∫⁻ x in M, ENNReal.ofReal C * ENNReal.ofReal (θ x) ∂μ := by
        refine setLIntegral_mono' hM fun x hx => ?_
        have hθx : 0 < θ x := hpos x hx
        have hn : ‖θ x • ζ x‖ ≤ C * θ x := by
          refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
          rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
            abs_of_pos hθx]
          calc θ x * |ζ x α| ≤ θ x * (C * ‖α‖) := by
                gcongr
                exact (hbound x α).trans (hcov α)
            _ = C * θ x * ‖α‖ := by ring
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC0]
        exact ENNReal.ofReal_le_ofReal hn
    _ = ENNReal.ofReal C * ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μ :=
        lintegral_const_mul _ hθ.ennreal_ofReal
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
```

## Key steps

1. θ•ζ is strongly measurable.
2. covectorEuclideanNorm α ≤ √(Pⁿ)·‖α‖, so ‖ζ(x)‖ ≤ √(Pⁿ) for every x.
3. On M, ‖θ(x)•ζ(x)‖ ≤ √(Pⁿ)·θ(x), so ∫⁻_M ‖θζ‖ₑ ≤ ofReal(√(Pⁿ))·∫⁻_M ofReal θ < ∞.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical); grep -n 'def unitBallVolume' and 'abbrev MultiVector' in the snapshot Contract.lean (lines 143, 48)`
- `grep -n 'theorem exists_disjoint_subfamily_covering_enlargement' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean (line 59)`
- `grep -n 'theorem hausdorffMeasure_le_liminf_tsum' and 'theorem hausdorffMeasure_apply' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (lines 555, 546)`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean (line 818)`
- `grep -n 'def vitaliFamily' and 'theorem tendsto_filterAt' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean (lines 1021, 1060)`
- `grep -rn 'theorem tendsto_tsum_compl_atTop_zero' <snapshot>/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ (ENNReal.lean line 235)`
- `grep -n 'countable_of_nonempty_interior' <snapshot>/mathlib/Mathlib/Topology/Bases.lean (line 493)`
- `grep -n 'exists_isOpen_lt_of_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean (line 359)`
- `grep -rn 'theorem le_iff' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/ (CompleteLattice.lean line 46: Measure.le_iff' is setwise for all sets)`
- `grep -n 'frequently_lt_of_lt_limsup' and 'eventually_lt_of_limsup_lt' <snapshot>/mathlib/Mathlib/Order/LiminfLimsup.lean (lines 646, 605)`
- `grep -n 'euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (def at line 68: μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `lean with LEAN_PATH from lake env on /tmp/gp-decomp/Check1.lean, Inst.lean, Inst2.lean, Api1.lean, Api2.lean (import GMT.Ch07.Submission): all cited lemmas reachable; HasBesicovitchCovering (Euclid P) and OuterRegular of finite measures found; Integrable τ μ for τ : Euclid P → MultiVector P n fails (ContinuousENorm not synthesized; the TopologicalSpace instance is ContinuousLinearMap.topologicalSpace, equal by rfl to the norm topology)`
- `lean on /tmp/gp-decomp/Final.lean and /tmp/gp-decomp/SubmissionInplace.lean: four child theorems proved from their exact frozen types, plus the parent assembly with the IB type as hypothesis; #print axioms gives propext, Classical.choice, Quot.sound`
- `python3 -I scan of dag.json: 1322 lean_names, none with prefix cbr_ci_gp_; the selected type and the cbr_ci_euclideanHausdorff_le_isodiametric type are equal to the strings used; inspected limsup/upper-density/covector nodes (regcomp_atl_upper_density_zero, idtp_dema_upper_density_zero, doraggt_ae_rescaled_lebesgue_point, regcomp_covector_*, cbr_lower_density_of_slice_property): no identical type to reuse`
- `git show 031b51256 (accepted Submission.regcomp_atl_upper_density_zero: Vitali + Measure.hausdorffMeasure_le_liminf_tsum pattern with crude constant 6^n)`
- `sed -n 1,100p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean (outerMeasure_le_tsum_of_fiveTimesCovering, simon_theorem_3_3: sharp-constant finite-tail argument, outside the contract import closure); Chapter06/Mass.lean covectorEuclideanNorm; Chapter06/Forms.lean Covector`
- `sed -n 560,735p and 1190,1240p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt (Simon 3.1-3.8, 3.26)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the four child types (all pass); leaf_verification.check_source_delta forbidden-token regex on the four proof bodies (no hits)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _render_parent_supplied_plan: children receive only their own sibling prerequisites)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-479700eeeb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/tmp/gp-decomp/Final.lean`
- `/tmp/gp-decomp/SubmissionInplace.lean`

Contract and reuse: the snapshot contract (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Submission.lean. Every Mathlib lemma used by the child proofs exists in the snapshot and is reachable from import GMT.Ch07.Submission. The SimonGMT formalization of Simon 3.3 is not importable from the contract, so density_comparison re-proves it and takes IB as an explicit hypothesis. No existing DAG declaration has an identical type, and the cbr_ci_gp_ names are fresh.

Instance finding: Integrable cannot be stated for MultiVector-valued maps with default instances, so the L1 data is passed as StronglyMeasurable plus a finite ∫⁻‖·‖ₑ.

Validation: all four child types elaborate in contract scope and pass the verifier's lexical check. Each child was proved sorry-free from its exact frozen type, compiled inside a copy of Submission.lean. The frozen parent type follows from upper_density, weighted_field and lebesgue_error together with the IB sibling. Only propext, Classical.choice and Quot.sound are used.
