# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.action_translation_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 3–5 of the parent proof ('Hence G' ≡ 0' and 'G(1) = G(0), i.e. S(ω(v + ·)) = S(ω)'), with the annihilation of step 4 taken as the hypothesis; this is the integrated (homotopy) form of Simon Ch. 6, 2.25 for h(t, x) = x + tv, and the translation counterpart of the accepted Submission.dtc_cwv_action_dilation_invariant. It uses the sibling translate_derivative.

1. (Translates are test forms.) For t ∈ ℝ put β_t(y) := ω(tv + y). ω is C^∞ and y ↦ tv + y is C^∞, so β_t is C^∞; y ↦ tv + y is a homeomorphism (Homeomorph.addLeft (tv)), so β_t has compact support (HasCompactSupport.comp_homeomorph). Thus β_t ∈ TestFormOn univ n.
2. (Derivative of a translate.) For every y, Dβ_t(y) = Dω(tv + y): the derivative of z ↦ ω(a + z) at y is Dω(a + y) (Mathlib fderiv_comp_add_left, a = tv).
3. (γ_t is a test form.) Put γ_t(y) := Dω(tv + y)[v]. Dω is C^∞ because ω is, so y ↦ Dω(tv + y) is C^∞, and applying it to the constant vector v gives a C^∞ map (ContDiff.clm_apply). Dω has compact support (HasCompactSupport.fderiv), hence so does y ↦ Dω(tv + y) (comp_homeomorph); and Dω(tv + y) = 0 forces γ_t(y) = 0, so support(γ_t) ⊆ support(y ↦ Dω(tv + y)) and γ_t has compact support (HasCompactSupport.mono). Thus γ_t ∈ TestFormOn univ n.
4. (Annihilation.) By step 2, γ_t(y) = Dω(tv + y)[v] = Dβ_t(y)[v] for every y, so the hypothesis with β = β_t and γ = γ_t gives R.action(γ_t) = 0, i.e. R.action(y ↦ Dω(tv + y)[v]) = 0.
5. (Zero derivative.) Let G(s) := R.action(y ↦ ω(sv + y)). By the sibling translate_derivative, G has derivative R.action(y ↦ Dω(tv + y)[v]) at t, which is 0 by step 4. As t was arbitrary, G is differentiable on ℝ with derivative 0 everywhere.
6. (Constancy.) A function ℝ → ℝ that is differentiable everywhere with zero derivative is constant (Mathlib is_const_of_deriv_eq_zero, a consequence of the mean value theorem); hence G(1) = G(0).
7. (Conclusion.) G(1) = R.action(y ↦ ω(1·v + y)) = R.action(y ↦ ω(v + y)) (one_smul), and G(0) = R.action(y ↦ ω(0·v + y)) = R.action(y ↦ ω(y)) = R.action(ω) (zero_smul, zero_add). Therefore R.action(y ↦ ω(v + y)) = R.action(ω). ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), like the accepted Submission theorems. #print axioms gives propext, Classical.choice, Quot.sound. It was also checked in isolation with only the listed sibling dependencies present (as stubs), and through the comparator's own NodeSolution wrapper (`exact Submission.X`).
- Do not put `open scoped ContDiff` in front of the declaration (it makes `ω` a reserved token); write the smoothness order as `(⊤ : ℕ∞)`, not `∞` (with `open scoped ENNReal`, `∞` is the ENNReal top).
- The sibling translate_derivative is `Submission.dimred_cs_ti_translate_action_hasDerivAt`.
```lean
/-- Translation invariance of `R.action` (the integrated form of `L_v S = 0`).  Suppose `R.action`
annihilates every directional derivative `y ↦ Dβ(y)[v]` of a test form `β`.  Put
`β_s(y) = ω(sv + y)` and `G(s) = R.action β_s`.  Its derivative
`G'(t) = R.action(Dω(tv + ·)[v]) = R.action(Dβ_t(·)[v])`
(`Submission.dimred_cs_ti_translate_action_hasDerivAt`) vanishes for every `t`, so `G` is constant
and `R.action(ω(v + ·)) = G(1) = G(0) = R.action ω`. -/
theorem Submission.dimred_cs_ti_action_translation_invariant : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), (∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = fderiv ℝ (β : DifferentialForm (Euclid P) n) y v) → R.action (γ : DifferentialForm (Euclid P) n) = 0) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, R.action (fun y => (ω : DifferentialForm (Euclid P) n) (v + y)) = R.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n R v hL ω
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  -- `β_t(y) = ω(tv + y)` is a test form
  have hβs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (ω : DifferentialForm (Euclid P) n) (t • v + y)) :=
    fun t => hws.comp (contDiff_const.add contDiff_id)
  have hβc : ∀ t : ℝ, HasCompactSupport
      (fun y => (ω : DifferentialForm (Euclid P) n) (t • v + y)) :=
    fun t => hwc.comp_homeomorph (Homeomorph.addLeft (t • v))
  -- chain rule: `Dβ_t(y) = Dω(tv + y)`
  have hfd : ∀ (t : ℝ) (y : Euclid P),
      fderiv ℝ (fun z => (ω : DifferentialForm (Euclid P) n) (t • v + z)) y =
        fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) :=
    fun t y => fderiv_comp_add_left (t • v)
  -- `γ_t(y) = Dω(tv + y)[v]` is a test form
  have hγs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v) := by
    intro t
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (ω : DifferentialForm (Euclid P) n)) :=
      hws.fderiv_right (by simp)
    exact (hd.comp (contDiff_const.add contDiff_id)).clm_apply contDiff_const
  have hγc : ∀ t : ℝ, HasCompactSupport
      (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v) := by
    intro t
    have h1 : HasCompactSupport
        (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y)) :=
      (hwc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft (t • v))
    refine h1.mono ?_
    intro y hy
    simp only [mem_support] at hy ⊢
    intro h0
    apply hy
    rw [h0]
    rfl
  -- `G(s) = R.action β_s` has derivative `R.action γ_t = 0` at every `t`
  let G : ℝ → ℝ := fun s => R.action (fun y => (ω : DifferentialForm (Euclid P) n) (s • v + y))
  have hG : ∀ t : ℝ, HasDerivAt G 0 t := by
    intro t
    have hD := Submission.dimred_cs_ti_translate_action_hasDerivAt P n R ω v t
    let β : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => (ω : DifferentialForm (Euclid P) n) (t • v + y), ⟨hβs t, hβc t⟩, subset_univ _⟩
    let γ : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v, ⟨hγs t, hγc t⟩,
        subset_univ _⟩
    have hγ0 : R.action (γ : DifferentialForm (Euclid P) n) = 0 :=
      hL β γ (fun y => by
        change fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v =
          fderiv ℝ (fun z => (ω : DifferentialForm (Euclid P) n) (t • v + z)) y v
        rw [hfd t y])
    have h0 : R.action (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v) = 0 :=
      hγ0
    rw [h0] at hD
    exact hD
  -- `G` is constant on `ℝ`
  have hconst : G 1 = G 0 :=
    is_const_of_deriv_eq_zero (fun t => (hG t).differentiableAt) (fun t => (hG t).deriv) 1 0
  have hG1 : G 1 = R.action (fun y => (ω : DifferentialForm (Euclid P) n) (v + y)) := by
    simp [G]
  have hG0 : G 0 = R.action (ω : DifferentialForm (Euclid P) n) := by
    simp [G]
  rw [← hG1, hconst, hG0]
```

## Key steps

1. β_t = ω(tv + ·) and γ_t = Dω(tv + ·)[v] are test forms, and Dβ_t(y) = Dω(tv + y) (fderiv_comp_add_left), so γ_t = Dβ_t[v].
2. The hypothesis gives R.action(γ_t) = 0, so by translate_derivative G(s) = R.action(ω(sv + ·)) has derivative 0 at every t.
3. G is constant (is_const_of_deriv_eq_zero), so R.action(ω(v + ·)) = G(1) = G(0) = R.action(ω).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c); git status (clean at b4d606d); stat GMT/Ch07/Submission.lean .lake/build/lib/lean/GMT/Ch07/Submission.olean`
- `python3 inspection of dag.json: selected node (depth 3, depends_on orientation_norm_bound-a1, no children), siblings under cone_splitting-a1, accepted dtc_cwv_* / dtc_cone_* / unit_orientation_norm_le_one / dtc_blowUp_testForm_corr types; scan of all lean_statements for curryLeft|blowUp|translat|fderiv|extDeriv|exteriorDerivative|HasDerivAt`
- `git show {d120e82,9203aee,77ba671,ec0cc8f,dd88db7,81f1c23,da8da23,0325970}:GMT/Ch07/Submission.lean (accepted cone criterion, wedge vanishing, Euler-Cartan, contraction, Lie annihilation, scaled derivative, dilation invariance, orientation norm proofs)`
- `python3 nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json and nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json (reuse convention, embedded-proof precedent)`
- `grep -rn 'alternatizeUncurryFin|extDeriv' and grep -rln 'Cartan|interiorProduct|lieDerivForm' in the snapshot mathlib (only Lie-algebra Cartan files; no Cartan formula or interior product for differential forms)`
- `grep -n defs in simongmt Chapter06/Forms.lean, AffineCurrentPushforward.lean, CurrentLocalEquality.lean (restrictDomain_apply); grep -rn 'curryLeft|interior|translat' simongmt (no contraction/translation lemmas)`
- `sed -n 330,400p book/chapter-07.txt (7.3.1 proof, Lemma 7.3.5 left to reader); sed -n 420,500p and 550,600p book/chapter-06.txt (homotopy formula 2.25-2.27, Lemma 2.33)`
- `#check fderiv_comp_add_left, is_const_of_deriv_eq_zero, exteriorDerivative_isTestForm, GeometricCurrentOn.boundary_apply, ContinuousAlternatingMap.curryLeftLI, ContinuousAlternatingMap.alternatizeUncurryFin`
- `verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope/child_modules applied to the 8 types (NodeChallenge/NodeSolution emulation)`
- `lake env lean /tmp/ti-decomp/{Stubs,Full2,Emu}.lean and /tmp/ti-decomp/final/{Final,Isolate,FromJson}.lean (all children, isolation with dependency stubs, comparator wrapper, re-extraction from JSON; #print axioms)`
- `grep -rl dimred_cs_ti_ across workspaces/ (incl. .swarm-worktrees), lake-packages simongmt, and dag.json (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-invariance-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-invariance-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ti-decomp/final/FromJson.lean`
- `/tmp/ti-decomp/final/Isolate.lean`
- `/tmp/ti-decomp/Emu.lean`

The pins match: the snapshot is at project b4d606d (= the workspace HEAD, clean) and mathlib 25730c7c. The built Submission.olean is newer than the frozen source.

What the library lacks.
- Mathlib has the exterior derivative (extDeriv = alternatizeUncurryFin ∘ fderiv, with extDeriv_apply and alternatizeUncurryFin_apply). It has no interior product and no Cartan formula for differential forms; the Cartan grep matches only Lie-algebra files.
- SimonGMT Chapter06 provides exteriorDerivative, IsTestForm, exteriorDerivative_isTestForm, boundary_apply, restrictDomain_apply, affinePushforward_apply and affinePullbackForm. It has no contraction, translation or Lie-derivative lemmas.
So the constant-field Cartan identity, the contraction lemma and the translation lemmas are new obligations.

Precedent and reuse.
- The accepted cone-lemma children (commits d120e82, 9203aee, 77ba671, ec0cc8f, dd88db7, 81f1c23, da8da23) prove the Euler-field (dilation) versions. Their types are tied to the point x or to sⁿω(s·), so none applies to a fixed vector v; they served as templates.
- The accepted dtc_blowUp_testForm_corr is not needed, because blowup_translate_eval unfolds blowUp directly.
- The only reuse is unit_orientation_norm_le_one (accepted, candidate 0325970, byte-identical type), which is already this node's resolved dependency.

Mathlib facts used, all present in the snapshot: fderiv_comp_add_left, is_const_of_deriv_eq_zero, HasCompactSupport.comp_homeomorph, HasCompactSupport.fderiv, hasDerivAt_integral_of_dominated_loc_of_deriv_le, Submodule.starProjection_eq_self_iff, ae_withDensity_iff and withDensity_absolutelyContinuous.

Lean check. All seven new children have kernel-checked proofs with standard axioms only, and the 9-line assembly of the frozen parent type compiles from them.
