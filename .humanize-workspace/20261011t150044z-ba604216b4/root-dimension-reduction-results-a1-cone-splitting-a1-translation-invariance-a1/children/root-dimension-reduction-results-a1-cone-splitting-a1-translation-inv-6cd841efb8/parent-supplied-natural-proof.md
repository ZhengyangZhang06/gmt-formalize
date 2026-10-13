# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.tangent_wedge_vanishes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2 of the parent proof (v ∧ ξ = 0): the translation analogue of 'x ∈ T_x spt C for μ_C-a.e. x, so in particular x ∧ C⃗ = 0' in Simon's proof of 7.3.1 (chapter-07.txt lines 355–358). It is the argument of the accepted Submission.dtc_cone_wedge_vanishes with the point x replaced by the fixed vector v.

1. (Orientation holds μ-a.e.) The field R.orients says: for Hⁿ⌞M-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ(x)) Q. Since μ = (Hⁿ⌞M).withDensity θ is absolutely continuous with respect to Hⁿ⌞M (withDensity_absolutelyContinuous), this also holds μ-a.e. Intersecting with the hypothesis, it suffices to fix x such that (a) p_{T_x}(v) = v, where T_x := approxTangentPlane n M x, and (b) there are Q as above and an orthonormal family τ = (τ_1, …, τ_n) with span(range τ) = Q and either ξ(x)(α) = α(τ) for every n-covector α or ξ(x)(α) = −α(τ) for every n-covector α; and to fix an (n+1)-covector β.
2. (T_x = Q.) Since some Q' satisfies HasApproximateTangentSpaceAt n M x Q' (namely Q), approxTangentPlane n M x is, by its definition, the subspace chosen by Classical.choose from this existence statement; approximate tangent spaces are unique (HasApproximateTangentSpaceAt.unique), so T_x = Q.
3. (v ∈ Q.) By (a) and step 2, p_Q(v) = v, hence v ∈ Q (Submodule.starProjection_eq_self_iff).
4. (y ↦ β(y, τ) vanishes on Q.) Put λ(y) := (β.curryLeft y)(τ) = β(y, τ_1, …, τ_n). It is linear in y (curryLeft is linear). For each j, λ(τ_j) = β(τ_j, τ_1, …, τ_n) = 0, because the entries in positions 0 and j + 1 coincide and β is alternating (map_eq_zero_of_eq). By span induction (λ(0) = 0, λ(y + z) = λ(y) + λ(z), λ(a·y) = a·λ(y)), λ vanishes on span(range τ) = Q.
5. (Conclusion.) By steps 3 and 4, (β.curryLeft v)(τ) = λ(v) = 0. In the first sign case ξ(x)(β.curryLeft v) = (β.curryLeft v)(τ) = 0; in the second, ξ(x)(β.curryLeft v) = −(β.curryLeft v)(τ) = −0 = 0. ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), like the accepted Submission theorems. #print axioms gives propext, Classical.choice, Quot.sound. It was also checked in isolation with only the listed sibling dependencies present (as stubs), and through the comparator's own NodeSolution wrapper (`exact Submission.X`).
- Do not put `open scoped ContDiff` in front of the declaration (it makes `ω` a reserved token); write the smoothness order as `(⊤ : ℕ∞)`, not `∞` (with `open scoped ENNReal`, `∞` is the ENNReal top).
```lean
/-- `v ∧ ξ(x) = 0` a.e. when `v` lies in the approximate tangent plane a.e. (the translation part of
the proof of Simon Lemma 7.3.5): `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM`, and
`y ↦ β(y, τ₁, …, τₙ)` is linear and vanishes on each `τᵢ` (repeated entry), hence on `TₓM ∋ v`. -/
theorem Submission.dimred_cs_ti_wedge_vanishes : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (v : Euclid P), (∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection v = v) → ∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β v) = 0 := by
  intro P n U R v hproj
  filter_upwards [hproj, (withDensity_absolutelyContinuous _ _).ae_le R.orients]
    with x hx hor β
  obtain ⟨Q, hQ, τ, -, hspan, hξ⟩ := hor
  have hT : approxTangentPlane n R.carrier x = Q := by
    have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec.unique hQ
  have hvQ : v ∈ Q := hT ▸ Submodule.starProjection_eq_self_iff.mp hx
  have hβ : ∀ y ∈ Q, ContinuousAlternatingMap.curryLeft β y τ = 0 := by
    intro y hy
    rw [← hspan] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      exact β.map_eq_zero_of_eq _ (i := 0) (j := b.succ) (by simp) (Fin.succ_ne_zero b).symm
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, ContinuousAlternatingMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy =>
      rw [map_smul, ContinuousAlternatingMap.smul_apply, hy, smul_zero]
  rcases hξ with hξ | hξ
  · rw [hξ, hβ v hvQ]
  · rw [hξ, hβ v hvQ, neg_zero]
```

## Key steps

1. Transfer R.orients from Hⁿ⌞M to μ = θHⁿ⌞M (absolute continuity) and intersect with the tangency hypothesis.
2. approxTangentPlane n M x = Q by uniqueness of approximate tangent spaces, so p_Q(v) = v gives v ∈ Q = span τ.
3. y ↦ β(y, τ_1, …, τ_n) is linear and vanishes on each τ_j (repeated entry), hence on Q ∋ v; so ξ(x)(β.curryLeft v) = ±β(v, τ) = 0.

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
