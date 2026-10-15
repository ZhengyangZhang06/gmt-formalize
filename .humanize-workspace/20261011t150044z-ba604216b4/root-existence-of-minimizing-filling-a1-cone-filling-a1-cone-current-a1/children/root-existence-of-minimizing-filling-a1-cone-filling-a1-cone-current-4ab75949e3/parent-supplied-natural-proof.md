# Parent-supplied natural-language proof

- Parent DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1`
- Child DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1.homotopy_toolkit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1(b), 1(c), 1(d) and the estimate of Step 4(c) of the selected parent's supplied proof (Parts B1 and B4). That is Simon Ch. 6, 2.25 and 2.30 at the level of forms (book/chapter-06.txt lines 441–451 and 528–551). The estimate of Step 4(c) is carried out in the Euclidean coefficient norm |·|_E rather than the operator norm, using the comparator-accepted siblings:
- covector_bound (Minkowski's integral inequality for |·|_E);
- curry_norm (|ι_xα|_E ≤ ‖x‖·|α|_E);
- norm_props (homogeneity |tα|_E = |t|·|α|_E).

Notation.
- E := ℝ^P = Euclid P and Λ^k := Covector E k.
- ι_xα := α.curryLeft x. Then ι_xα(v) = α(Fin.cons x v) (ContinuousAlternatingMap.curryLeft_apply_apply; Matrix.vecCons x v is Fin.cons x v by definition).
- α ↦ α.curryLeft is the linear isometry curryLeftLI, additive and homogeneous (curryLeft_add, curryLeft_smul, curryLeft_zero).
- |α|_E := covectorEuclideanNorm α.
- For a continuous (m+1)-form γ and x ∈ E, put f^γ_x(t) := t^m • ι_xγ(tx) ∈ Λ^m and Kγ(x) := ∫_0^1 f^γ_x(t) dt (interval integral over [0, 1]).

0. Continuity of the integrand. For every continuous γ and every x, t ↦ f^γ_x(t) is continuous:
 - t ↦ tx is continuous and γ is continuous;
 - curryLeftLI is continuous linear, and evaluating the resulting continuous linear map at the fixed x is continuous (Continuous.clm_apply);
 - t ↦ t^m and scalar multiplication are continuous.
 Hence f^γ_x is interval integrable on [0, 1] (Continuous.intervalIntegrable).

1. Evaluation (conclusion (1)). Fix x and v : Fin m → E. ev_v : Λ^m → ℝ, α ↦ α(v), is continuous linear (ContinuousAlternatingMap.apply ℝ E ℝ v). By step 0 and ContinuousLinearMap.intervalIntegral_comp_comm,
 (E1) Kβ(x)(v) = ev_v(∫_0^1 f^β_x(t) dt) = ∫_0^1 f^β_x(t)(v) dt.
 Pointwise, f^β_x(t)(v) = t^m·ι_xβ(tx)(v) = t^m·β(tx)(Fin.cons x v) (ContinuousAlternatingMap.smul_apply, curryLeft_apply_apply). Hence Kβ(x)(v) = ∫_0^1 t^m·β(tx)(Fin.cons x v) dt.

2. Coefficient-norm bound (conclusion (2)). Let c ∈ ℝ with |β(y)|_E ≤ c for every y ∈ E, and fix x. Apply the sibling covector_bound with N := P, k := m, α := Kβ(x), f := f^β_x and the constant ‖x‖·c. Its hypotheses hold:
 - f^β_x is continuous (step 0);
 - α(v) = ∫_0^1 f^β_x(t)(v) dt for every v, by (E1);
 - for t ∈ [0, 1]:
 |f^β_x(t)|_E = |t^m|·|ι_xβ(tx)|_E (norm_props (ii))
 ≤ |t^m|·(‖x‖·|β(tx)|_E) (curry_norm, and |t^m| ≥ 0)
 ≤ 1·(‖x‖·|β(tx)|_E) (|t^m| = t^m ≤ 1 because 0 ≤ t ≤ 1, and ‖x‖·|β(tx)|_E ≥ 0)
 ≤ ‖x‖·c (‖x‖ ≥ 0 and |β(tx)|_E ≤ c).
 Hence |Kβ(x)|_E ≤ ‖x‖·c.

3. Vanishing (conclusion (3)). Suppose β(tx) = 0 for every t ∈ [0, 1]. For t ∈ uIcc 0 1 = [0, 1], f^β_x(t) = t^m•ι_x0 = t^m•0 = 0 (curryLeft_zero). The interval integral depends only on the integrand on uIcc 0 1 (intervalIntegral.integral_congr), so Kβ(x) = ∫_0^1 0 dt = 0.

4. Additivity (conclusion (4)). Let β' be continuous and fix x. For every t, (β + β')(tx) = β(tx) + β'(tx). So ι_x(β + β')(tx) = ι_xβ(tx) + ι_xβ'(tx) (curryLeft_add, evaluation of a sum of continuous linear maps), and f^{β+β'}_x(t) = f^β_x(t) + f^{β'}_x(t) (smul_add). Both summands are interval integrable by step 0, so intervalIntegral.integral_add gives K(β + β')(x) = Kβ(x) + Kβ'(x).

5. Homogeneity (conclusion (5)). Let c ∈ ℝ. For every t, (cβ)(tx) = c•β(tx), so ι_x(cβ)(tx) = c•ι_xβ(tx) (curryLeft_smul) and f^{cβ}_x(t) = t^m•(c•ι_xβ(tx)) = c•f^β_x(t) (smul_comm). intervalIntegral.integral_smul needs no integrability and gives K(cβ)(x) = c•Kβ(x). ∎

Lean implementation note. The proof below was compiled during decomposition after `import GMT.Ch07.Submission` in namespace GMT.Ch07 with the contract's opens. It uses the three sibling types only. With their accepted proofs spliced in, #print axioms gives propext, Classical.choice, Quot.sound.

```lean
theorem Submission.ecf_cc_radial_homotopy_toolkit : ∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)), Continuous β → (∀ (x : Euclid P) (v : Fin m → Euclid P), (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) v = ∫ t in (0 : ℝ)..1, t ^ m * β (t • x) (Fin.cons x v)) ∧ (∀ (c : ℝ) (x : Euclid P), (∀ y : Euclid P, covectorEuclideanNorm (β y) ≤ c) → covectorEuclideanNorm (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) ≤ ‖x‖ * c) ∧ (∀ x : Euclid P, (∀ t ∈ Icc (0 : ℝ) 1, β (t • x) = 0) → (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) = 0) ∧ (∀ β' : DifferentialForm (Euclid P) (m + 1), Continuous β' → ∀ x : Euclid P, (∫ t in (0 : ℝ)..1, t ^ m • ((β + β') (t • x)).curryLeft x) = (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) + ∫ t in (0 : ℝ)..1, t ^ m • (β' (t • x)).curryLeft x) ∧ ∀ (c : ℝ) (x : Euclid P), (∫ t in (0 : ℝ)..1, t ^ m • ((c • β) (t • x)).curryLeft x) = c • ∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x := by
  intro P m β hβ
  -- Step 0: the integrand is continuous in `t`
  have hf : ∀ γ : DifferentialForm (Euclid P) (m + 1), Continuous γ → ∀ x : Euclid P,
      Continuous (fun t : ℝ => t ^ m • (γ (t • x)).curryLeft x) := by
    intro γ hγ x
    have h1 : Continuous (fun t : ℝ => γ (t • x)) := hγ.comp (continuous_id.smul continuous_const)
    have h2 : Continuous (fun t : ℝ => (γ (t • x)).curryLeft) :=
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ) (n := m)).continuous.comp h1
    exact (continuous_pow m).smul (h2.clm_apply continuous_const)
  -- Step 1: evaluation commutes with the integral
  have heval : ∀ (x : Euclid P) (v : Fin m → Euclid P),
      (∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) v =
        ∫ t in (0 : ℝ)..1, (t ^ m • (β (t • x)).curryLeft x) v := by
    intro x v
    exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v).intervalIntegral_comp_comm
      ((hf β hβ x).intervalIntegrable 0 1)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x v
    rw [heval x v]
    congr 1
  · intro c x hc
    refine Submission.cmcdt_lpo_slice_covector_bound P m _ (fun t => t ^ m • (β (t • x)).curryLeft x)
      (‖x‖ * c) (hf β hβ x) (heval x) ?_
    intro t ht
    rw [(Submission.rsd_mw_tfa_norm_props P m).2.1]
    have h1 := Submission.cmcdt_lp_covector_curryLeft_norm_le P m x (β (t • x))
    have h2 : |t ^ m| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg ht.1 m)]
      exact pow_le_one₀ ht.1 ht.2
    have h3 : ‖x‖ * covectorEuclideanNorm (β (t • x)) ≤ ‖x‖ * c :=
      mul_le_mul_of_nonneg_left (hc _) (norm_nonneg x)
    calc |t ^ m| * covectorEuclideanNorm ((β (t • x)).curryLeft x)
        ≤ 1 * (‖x‖ * covectorEuclideanNorm (β (t • x))) :=
          mul_le_mul h2 h1 (covectorEuclideanNorm_nonneg _) zero_le_one
      _ ≤ ‖x‖ * c := by rw [one_mul]; exact h3
  · intro x hx
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : Covector (Euclid P) m)) ?_]
    · simp
    · intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only
      rw [hx t ht, ContinuousAlternatingMap.curryLeft_zero, ContinuousLinearMap.zero_apply, smul_zero]
  · intro β' hβ' x
    rw [← intervalIntegral.integral_add ((hf β hβ x).intervalIntegrable 0 1)
      ((hf β' hβ' x).intervalIntegrable 0 1)]
    congr 1
    funext t
    rw [Pi.add_apply, ContinuousAlternatingMap.curryLeft_add, ContinuousLinearMap.add_apply, smul_add]
  · intro c x
    rw [← intervalIntegral.integral_smul]
    congr 1
    funext t
    rw [Pi.smul_apply, ContinuousAlternatingMap.curryLeft_smul, ContinuousLinearMap.smul_apply, smul_comm]
```

## Key steps

1. t ↦ t^m • ι_xβ(tx) is continuous (β continuous, curryLeftLI continuous linear), hence interval integrable on [0, 1].
2. Evaluation at v is continuous linear and commutes with the interval integral; smul_apply and curryLeft_apply_apply give Kβ(x)(v) = ∫_0^1 t^m β(tx)(Fin.cons x v) dt (conclusion (1)).
3. covector_bound with |t^m • ι_xβ(tx)|_E = |t^m|·|ι_xβ(tx)|_E ≤ ‖x‖·|β(tx)|_E ≤ ‖x‖c on [0, 1] (norm_props, curry_norm) gives |Kβ(x)|_E ≤ ‖x‖c (conclusion (2)).
4. If β vanishes on [0, 1]·x the integrand vanishes on uIcc 0 1, so Kβ(x) = 0 by integral_congr (conclusion (3)).
5. curryLeft_add/curryLeft_smul with intervalIntegral.integral_add (integrable summands) and integral_smul give additivity and homogeneity (conclusions (4), (5)).

## Reference use

### local-project

Queries:
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (all three e4148e7f9503aa28930a…; manifest: project b4d606db, Mathlib 25730c7c)`
- `grep -n in local-references/123e8435b4a2469b/mathlib/Mathlib: curryLeft_apply_apply|curryLeft_add|curryLeft_smul|curryLeft_zero|curryLeftLI (Analysis/Normed/Module/Alternating/Curry.lean); def alternatizeUncurryFin|alternatizeUncurryFinCLM_apply|alternatizeUncurryFin_smul (Analysis/Normed/Module/Alternating/Uncurry/Fin.lean); def extDeriv|extDeriv_smul|EventuallyEq.extDeriv_eq|extDeriv_apply (Analysis/Calculus/DifferentialForm/Basic.lean); isClosedMap_snd_of_compactSpace (Topology/Maps/Proper/Basic.lean:337); instance compactSpace_Icc (Topology/Order/Compact.lean:113); HasCompactSupport.smul_right (Topology/Algebra/Support.lean:466); ContDiff.fderiv_right (Analysis/Calculus/ContDiff/Comp.lean:750); IsBounded.subset_closedBall (Topology/MetricSpace/Bounded.lean:101); def apply (Topology/Algebra/Module/Alternating/Topology.lean:294); exists_contDiff_support_eq_eq_one_iff`
- `python3 -I over dag.json (2416 nodes): regex scans homotop|curryLeft|Poincar|cutoff|covectorEuclideanNorm|EqOn|Disjoint … → X.support ⊆|∃ ζ … ContDiff … = 1; status, candidate_commit and child/dependency closure of the 10 reuse targets; byte equality of their lean_statement; absence of ecf_cc_radial_homotopy_formula and ecf_cc_radial_homotopy_toolkit`
- `git show <candidate>:GMT/Ch07/Submission.lean for the 10 reused candidates: exact `theorem Submission.X : <frozen type> := by` header, contract prefix identical to the workspace contract, only sorry is main_theorem, 13 distinct theorem names`
- `sed of /runtime/flows/gmt-claude-a72bcd2dc14b/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint) and prompts.py (DECOMPOSE, DECOMPOSITION_AUDIT, SPECULATIVE_PARENT_TASK)`
- `cat .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,FormSupNorm}.lean`
- `sed -n 441,456p and 528,551p book/chapter-06.txt (Simon 6.2.25, 2.30–2.32)`
- `lean (LEAN_PATH = local copy of the lake libraries) on /tmp/cone-current-split/lean/{Probe,Types,Assembly,AssemblyAx,ProofA,ProofB,TC,Full}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-f92df94753/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-14afd577b6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-82644d9359/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9b01f284ba/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-a72bcd2dc14b/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-a72bcd2dc14b/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cone-current-split/lean/Types.lean`
- `/tmp/cone-current-split/lean/Assembly.lean`
- `/tmp/cone-current-split/lean/ProofA.lean`
- `/tmp/cone-current-split/lean/ProofB.lean`
- `/tmp/cone-current-split/lean/Full.lean`

The snapshot is project b4d606db with Mathlib 25730c7c. Its Ch07 Contract.lean is byte-identical (sha256 e4148e7f9503aa28930a…) to the workspace Contract.lean and Submission.lean, so the child types are checked against the frozen contract.

Snapshot contents:
- The pinned Mathlib supplies every tool the new children and the assembly cite: curryLeft, curryLeftLI, curryLeft_apply_apply/add/smul/zero, alternatizeUncurryFin(CLM) with alternatizeUncurryFin_smul, extDeriv = alternatizeUncurryFin ∘ fderiv, extDeriv_smul, Filter.EventuallyEq.extDeriv_eq, ContinuousAlternatingMap.apply, ContinuousLinearMap.intervalIntegral_comp_comm, intervalIntegral.integral_eq_sub_of_hasDerivAt, isClosedMap_snd_of_compactSpace, compactSpace_Icc, HasCompactSupport.smul_right, ContDiff.fderiv_right and Bornology.IsBounded.subset_closedBall.
- Neither Mathlib nor SimonGMT has a Poincaré homotopy operator, cone current or homotopy formula for forms, so homotopy_formula and homotopy_toolkit are genuine new obligations.
- SimonGMT Chapter06 supplies the frozen objects GeometricCurrentOn, TestFormOn, boundary (boundary_apply) and exteriorDerivativeTestOn, plus covectorEuclideanNorm, massOn/mass, support/zeroRegion and GeometricCurrentOn.ext.

DAG scan (2416 nodes): ten accepted checkpoints match steps of the supplied proof with exactly usable types. They are cmcdt_lpo_slice_param_integral, dtc_cone_euler_cartan, cmcdt_lpo_slice_covector_bound, cmcdt_lp_covector_curryLeft_norm_le, rsd_mw_tfa_norm_props, cbrcs_ce_smooth_cutoff, cmr_abs_apply_le_massOn, cmcdt_lpo_tk_bounded_current, dtc_vanish_off_support and rsd_cmr_support_subset_of_vanish.
- Their frozen types are byte-identical to the reused children.
- Their candidate commits contain those exact headers, and the only sorry is main_theorem.
- Their closures are accepted.

Lean checks:
- All child types elaborate.
- A sorry-free chain built from the accepted candidate proofs, the two new proofs and the parent assembly compiles with propext, Classical.choice and Quot.sound only.
- One pitfall: Lean cannot synthesize ENormedAddMonoid on Euclid P →L[ℝ] Covector … The new children's compiled proofs avoid this with helper statements over generic normed spaces.
