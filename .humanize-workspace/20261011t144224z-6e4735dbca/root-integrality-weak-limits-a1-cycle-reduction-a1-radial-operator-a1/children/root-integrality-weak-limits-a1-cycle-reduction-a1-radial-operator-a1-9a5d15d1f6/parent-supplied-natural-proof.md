# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1, 2 and 6 of the parent proof (interior product as a bounded bilinear map, smoothness of the integrand, first derivative), filled in. A Lean rendering of exactly this argument was compiled against the pinned snapshot, using only the standard axioms.

Conventions. E := Eucl P, Λ_l := Covector E l, and (y, v) := Fin.cons y v. For α ∈ Λ_{k+1}, α.curryLeft ∈ E →L[ℝ] Λ_k satisfies (α.curryLeft w)(u) = α(Matrix.vecCons w u) (ContinuousAlternatingMap.curryLeft_apply_apply), and Matrix.vecCons w u = Fin.cons w u holds definitionally.

1. (Interior product as a bounded linear map.) Let 𝔅 := (ContinuousAlternatingMap.curryLeftLI).toContinuousLinearMap : Λ_{k+1} →L[ℝ] (E →L[ℝ] Λ_k). Then 𝔅(α) = α.curryLeft for every α, definitionally. Hence:
 - F(p) := p.1^a • (ω(p.1 • p.2)).curryLeft p.2 = p.1^a • 𝔅(ω(p.1 • p.2))(p.2);
 - for each fixed t, f_t(z) := t^a • (ω(t • z)).curryLeft z = t^a • 𝔅(ω(t • z))(z).

2. (Joint smoothness.) Build F in five steps:
 - p ↦ p.1 • p.2 on ℝ × E is C^∞, as the scalar multiple of the C^∞ projections (contDiff_fst.smul contDiff_snd);
 - composing with the C^∞ map ω, p ↦ ω(p.1 • p.2) is C^∞ (ContDiff.comp);
 - composing with the continuous linear map 𝔅, p ↦ 𝔅(ω(p.1 • p.2)) ∈ E →L[ℝ] Λ_k is C^∞;
 - applying it to the C^∞ map p ↦ p.2, p ↦ 𝔅(ω(p.1 • p.2))(p.2) is C^∞ (ContDiff.clm_apply);
 - multiplying by the C^∞ scalar function p ↦ p.1^a (contDiff_fst.pow a) shows F is C^∞ (ContDiff.smul).
 By Step 1 this is the first conjunct.

3. (First derivative.) Fix t ∈ ℝ and x ∈ E, and write A := fderiv ℝ ω (t • x).
 (a) z ↦ t • z has derivative t • id_E at x ((hasFDerivAt_id x).const_smul t).
 (b) ω is C^∞, hence differentiable at t • x with derivative A.
 (c) By the chain rule, c(z) := 𝔅(ω(t • z)) has derivative c' := 𝔅 ∘L (A ∘L (t • id_E)) at x (𝔅.hasFDerivAt.comp and HasFDerivAt.comp).
 (d) By the product rule for evaluating an operator-valued map (HasFDerivAt.clm_apply with u = id, u' = id_E), z ↦ c(z)(z) has derivative L := c(x) ∘L id_E + c'.flip x at x. Thus L(w) = c(x)(w) + c'(w)(x) = 𝔅(ω(t•x))(w) + 𝔅(A(t • w))(x).
 (e) Multiplying by the constant t^a (HasFDerivAt.const_smul), f_t has derivative t^a • L at x. So fderiv ℝ f_t x = t^a • L.

4. (Evaluation.) For w ∈ E and v ∈ E^k:
 fderiv ℝ f_t x w v
 = t^a · L(w)(v)
 = t^a · (𝔅(ω(t•x))(w)(v) + 𝔅(A(t • w))(x)(v))
 = t^a · (ω(t•x)(Fin.cons w v) + (A(t • w))(Fin.cons x v)).
 A is linear, so A(t • w) = t • A(w) and (A(t • w))(Fin.cons x v) = t · A(w)(Fin.cons x v). Commuting the two summands gives
 fderiv ℝ f_t x w v = t^a · (t · fderiv ℝ ω (t • x) w (Fin.cons x v) + ω(t • x)(Fin.cons w v)),
 which is the second conjunct. ∎

Implementation notes (all checked in a scratch build against the snapshot):
- No extra imports are needed.
- Put `set_option maxSynthPendingDepth 3 in` before the theorem. Without it, `ContinuousLinearMap.hasFDerivAt` applied to 𝔅 fails with an instance-path mismatch between the algebraic and normed instances on Λ_{k+1} →L (E →L Λ_k).
- Introduce 𝔅 opaquely: `obtain ⟨B, hB⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k), ∀ α, B α = α.curryLeft := ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ) (n := k)).toContinuousLinearMap, fun α => rfl⟩`. A `set` abbreviation of the same map caused unification timeouts. Rewrite the two functions with `funext; rw [hB]`.
- `fun_prop` fails here because `ω : DifferentialForm …` is not syntactically a function, so compose the ContDiff lemmas by hand.
- State the result of `HasFDerivAt.const_smul` with the explicit pointwise function `fun z => t ^ a • B (ω (t • z)) z`. Otherwise Lean produces the function-level `t ^ a • fun y => …`.
- Finish with `rw [hf.fderiv]`, then a `simp only` using the smul/add/comp/id/flip apply-lemmas for continuous linear and alternating maps together with `hB`, `ContinuousAlternatingMap.curryLeft_apply_apply`, `map_smul` and `smul_eq_mul`, and then `rw [add_comm]; rfl`.

Appendix — verified Lean rendering of the proof above. It was compiled against the pinned snapshot in the Submission.lean layout, i.e. inside `namespace GMT.Ch06` after the contract's section, with the contract's `open`s. A comparator-style check `theorem … : (frozen type) := by exact Submission.<name>`, run in the replayed contract scope, also passes. `#print axioms` reports only propext, Classical.choice and Quot.sound. No extra import is required.

```lean
set_option maxSynthPendingDepth 3 in
theorem Submission.iwl_cr_ro_integrand_contDiff_fderiv :
    (∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) ∧ ∀ (t : ℝ) (x w : Eucl P) (v : Fin k → Eucl P), fderiv ℝ (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x w v = t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v))) := by
  intro P k a ω hω
  obtain ⟨B, hB⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k),
      ∀ α, B α = α.curryLeft :=
    ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ) (n := k)).toContinuousLinearMap,
      fun α => rfl⟩
  refine ⟨?_, ?_⟩
  · have hfun : (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) =
        fun p => p.1 ^ a • B (ω (p.1 • p.2)) p.2 := by
      funext p; rw [hB]
    rw [hfun]
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => B (ω (p.1 • p.2))) :=
      B.contDiff.comp (hω.comp hs)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × Eucl P => B (ω (p.1 • p.2)) p.2) :=
      h1.clm_apply contDiff_snd
    exact (contDiff_fst.pow a).smul h2
  · intro t x w v
    have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
        fun z => t ^ a • B (ω (t • z)) z := by
      funext z; rw [hB]
    rw [hfun]
    have hω' : HasFDerivAt ω (fderiv ℝ ω (t • x)) (t • x) :=
      (hω.differentiable (by simp) (t • x)).hasFDerivAt
    have hs : HasFDerivAt (fun z : Eucl P => t • z) (t • ContinuousLinearMap.id ℝ (Eucl P)) x :=
      (hasFDerivAt_id x).const_smul t
    have hc : HasFDerivAt (fun z : Eucl P => B (ω (t • z)))
        (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))) x :=
      B.hasFDerivAt.comp x (hω'.comp x hs)
    have happ := hc.clm_apply (hasFDerivAt_id x)
    have hf : HasFDerivAt (fun z : Eucl P => t ^ a • B (ω (t • z)) z)
        (t ^ a • ((B (ω (t • x))).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
          (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))).flip x)) x :=
      happ.const_smul (t ^ a)
    rw [hf.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, hB,
      ContinuousAlternatingMap.curryLeft_apply_apply, map_smul, smul_eq_mul,
      ContinuousLinearMap.coe_id', id_eq, ContinuousAlternatingMap.curryLeft_smul]
    rw [add_comm]
    rfl
```

## Key steps

1. Interior product 𝔅 := curryLeftLI as a continuous linear map, so F(t,x) = t^a • 𝔅(ω(t•x))(x) and (α.curryLeft w)(u) = α(Fin.cons w u).
2. Joint C^∞: compose p ↦ p.1•p.2, ω and 𝔅, apply at p.2 (ContDiff.clm_apply), and multiply by p.1^a.
3. Chain rule for z ↦ 𝔅(ω(t•z)), product rule HasFDerivAt.clm_apply with u = id, then const_smul: the derivative is t^a • (𝔅(ω(tx)) + (𝔅∘Dω(tx)∘(t•id)).flip x).
4. Evaluate at w and v using curryLeft_apply_apply (vecCons = Fin.cons) and Dω(tx)[t•w] = t•Dω(tx)[w].

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; sha256sum GMT/Ch06/Contract.lean`
- `rg -n "(theorem|lemma|def|abbrev) [A-Za-z_.']*<name>\b" mathlib/Mathlib for <name> in hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, curryLeftLI, norm_curryLeft, curryLeft_apply_apply, iteratedFDeriv_comp_right, continuous_iteratedFDeriv, iteratedFDeriv_succ_eq_comp_left, continuous_parametric_intervalIntegral_of_continuous, contDiff_of_differentiable_iteratedFDeriv, intervalIntegral_comp_comm, norm_compContinuousLinearMap_le, norm_integral_le_of_norm_le_const, contDiff_parametric_integral_of_contDiff, contDiff_parametric_primitive_of_contDiff`
- `rg -n 'contDiff_parametric|ContDiff.*intervalIntegral|contDiff_integral|iteratedFDeriv_integral|integral_iteratedFDeriv|contDiffOn_parametric|fderiv_integral|hasFDerivAt_integral\b' mathlib/Mathlib`
- `rg -n 'parametric_primitive|parametric_integral|ParametricIntegral' mathlib/Mathlib`
- `rg -n 'norm_iteratedFDeriv_le_of_bilinear_of_le_one|norm_iteratedFDeriv_clm_apply|iteratedFDeriv_const_smul_apply|iteratedFDeriv_const_of_ne|theorem fderiv_id|prod_le_one₀|iteratedFDeriv_succ_eq_comp_right|contDiff_succ_iff_fderiv|contDiff_infty|iteratedFDeriv_one_apply|norm_iteratedFDeriv_one|intervalIntegral_comp_comm' mathlib/Mathlib`
- `rg -n 'def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `rg -n 'iteratedFDeriv_fixedSupportParameterSlice|intervalIntegral|∫ t in' simongmt/Poincare/SimonGMT; grep -n 'abbrev|^def' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3: dag.json node metadata and lean_name scan (iwl_cr_*, radial, lean_statements containing ∫ together with fderiv/iteratedFDeriv/ContDiff); grep -rl iwl_cr_ro_ over dag.json, nodes/ and GMT/; git grep -l iwl_cr_ro_ over all 619 ref tips`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (imports and Submission.X declaration layout of an accepted candidate)`
- `python3 -I /tmp/ro_split/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/ro_split/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/ro_split/scratch/{Assembly,Full,InstCheck,ImportCheck}.lean and /tmp/ro_split/snip/Snip{A,B1,B2}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ro_split/scripts/gen.py`
- `/tmp/ro_split/scratch/Assembly.lean`
- `/tmp/ro_split/scratch/Full.lean`
- `/tmp/ro_split/scratch/InstCheck.lean`
- `/tmp/ro_split/scratch/ImportCheck.lean`
- `/tmp/ro_split/snip/SnipA.lean`
- `/tmp/ro_split/snip/SnipB1.lean`
- `/tmp/ro_split/snip/SnipB2.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean (sha256 ea3ee0dd…).

Missing obligation. The snapshot Mathlib has only first-order differentiation under an interval integral (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, Analysis/Calculus/ParametricIntervalIntegral.lean:55) and continuity of parametric integrals (`continuous_parametric_intervalIntegral_of_continuous'`, DominatedConvergence.lean:619). There is no lemma for C^∞ smoothness of x ↦ ∫ G(t,x) dt or for iterated derivatives under the integral: the searches for contDiff_parametric*, ContDiff.*intervalIntegral and iteratedFDeriv_integral found nothing. So the all-order statement is a genuinely missing, reusable obligation, which becomes child parametric_integral.

Available Mathlib tools:
- Leibniz bounds `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear(_of_le_one)` (ContDiff/Bounds.lean:202/226);
- curryLeft, curryLeftLI, norm_curryLeft and curryLeft_apply_apply (Normed/Module/Alternating/Curry.lean);
- `ContinuousLinearMap.iteratedFDeriv_comp_right` (ContDiff/Basic.lean:461);
- `iteratedFDeriv_succ_eq_comp_right` and `iteratedFDeriv_one_apply` (FTaylorSeries.lean);
- `contDiff_succ_iff_fderiv` and `contDiff_infty` (ContDiff/Defs.lean);
- `ContinuousAlternatingMap.apply` and `ContinuousMultilinearMap.apply` (Topology/Algebra/Module/{Alternating,Multilinear}/Topology.lean).

Imports. ParametricIntervalIntegral and ContDiff.Bounds are not imported by GMT.Ch06.Submission (an #check reports unknown constants), so children 1 and 3 add those imports. The accepted candidate at commit 2f36576 also adds imports to Submission.lean and declares `theorem Submission.X` inside namespace GMT.Ch06.

SimonGMT. Covector and DifferentialForm are abbrevs (Chapter06/Forms.lean:31/37). `iteratedFDeriv_fixedSupportParameterSlice` (Chapter06/ParametricCurrentContinuity.lean:76) uses the same partial-derivative-by-inclusion pattern, but SimonGMT has no smoothness result for parametric integrals.

DAG and names. No DAG node supplies a parametric-integral smoothness lemma or the radial integrand facts. The names iwl_cr_ro_* and the helper prefixes iwl_cr_ro_pi_ / iwl_cr_ro_ib_ occur nowhere in dag.json, nodes/, GMT/ or any of the 619 git ref tips.

Lean checks:
- The three frozen child types, generated through the verifier's own child_modules / validate_lean_statement path, elaborate in the replayed contract scope.
- Assembly.lean proves the parent's exact frozen type from the three children, which are sorried there.
- Full.lean and Snip{A,B1,B2}.lean prove all three children and the parent; #print axioms gives [propext, Classical.choice, Quot.sound], and the comparator-style `exact Submission.<name>` targets pass.
- An independent reviewer agent re-ran these builds and accepted the split.

Public citations for the standard mathematics: differentiation under the integral sign (Dieudonné, Foundations of Modern Analysis, §8.11) and the radial homotopy operator of the Poincaré lemma (Spivak, Calculus on Manifolds, Thm 4-11).
