# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.dilation-a1.integer_multiplicity-a1`
- Child DAG node: `root.deformation-a1.dilation-a1.integer_multiplicity-a1.weighted_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 4 (weighted tangent transport), specialized and made self-contained. No sibling is used.

Conventions.
- ℝ^N := Eucl N and μ := μHE[k], the Hausdorff measure H^k on ℝ^N.
- M′ := (fun y => ρ • y) '' M = {ρ • z : z ∈ M} and θ′(y) := θ(ρ⁻¹ • y).
- blowUpMap p s w := s⁻¹ • (w − p). This is Poincare.SimonGMT.Chapter03.blowUpMap, Simon's η_{p,s}. It is not opened in the contract scope, so write it fully qualified.
- Definition (SimonGMT Chapter03.Rectifiable; Simon Ch. 3, 1.7). HasWeightedApproximateTangentSpaceAt k S ϑ p Q means:
  (A) finrank ℝ Q = k, and
  (B) for every f ∈ C_c(ℝ^N, ℝ), the function J(S, ϑ, p, f)(s) := ∫_{u ∈ blowUpMap p s '' S} f(u)·ϑ(p + s • u) dμ(u) tends to ϑ(p)·∫_{u ∈ Q} f(u) dμ(u) as s → 0 along 𝓝[>] 0.
- From ρ > 0 we get ρ ≠ 0 and ρ⁻¹ > 0 (inv_pos).
- Let hQ denote the hypothesis HasWeightedApproximateTangentSpaceAt k M θ x Q.

1. Dimension. Part (A) for (M′, θ′, ρ • x, Q) says finrank Q = k. This is part (A) of hQ.

2. New weight at the new point. θ′(ρ • x) = θ(ρ⁻¹ • (ρ • x)) = θ(x), because ρ⁻¹ • (ρ • x) = x for ρ ≠ 0 (inv_smul_smul₀).

3. Blow-up sets. Claim: for every real s, blowUpMap (ρ • x) s '' M′ = blowUpMap x (ρ⁻¹·s) '' M.
   By Set.image_image, the left side is the image of M under z ↦ s⁻¹ • (ρ • z − ρ • x). By Set.image_congr it suffices to show, for each z ∈ M,
   s⁻¹ • (ρ • z − ρ • x) = (ρ⁻¹·s)⁻¹ • (z − x).
   Left side: ρ • z − ρ • x = ρ • (z − x) (smul_sub), and s⁻¹ • (ρ • (z − x)) = (s⁻¹·ρ) • (z − x) (smul_smul).
   Right side: (ρ⁻¹·s)⁻¹ = s⁻¹·(ρ⁻¹)⁻¹ = s⁻¹·ρ (mul_inv_rev, inv_inv).
   These field identities hold under Lean's convention 0⁻¹ = 0, so the equality holds for every s, including s = 0.

4. Weights. For every real s and u ∈ ℝ^N:
   θ′(ρ • x + s • u) = θ(ρ⁻¹ • (ρ • x + s • u))
   = θ(ρ⁻¹ • ρ • x + ρ⁻¹ • s • u) (smul_add)
   = θ(x + (ρ⁻¹·s) • u) (inv_smul_smul₀, smul_smul).

5. Integral identity. Fix f ∈ C_c(ℝ^N, ℝ) and put I(s) := J(M, θ, x, f)(s). For every real s, rewrite the domain of integration by Step 3 and the integrand pointwise by Step 4:
   J(M′, θ′, ρ • x, f)(s) = ∫_{u ∈ blowUpMap x (ρ⁻¹·s) '' M} f(u)·θ(x + (ρ⁻¹·s) • u) dμ(u) = I(ρ⁻¹·s).

6. Reparametrization. Let g(s) := ρ⁻¹·s. Then g tends from 𝓝[>] 0 to 𝓝[>] 0:
   (a) g is continuous (continuous_const_mul) and g(0) = ρ⁻¹·0 = 0, so g tends from 𝓝 0 to 𝓝 0. Since 𝓝[>] 0 ≤ 𝓝 0 (nhdsWithin_le_nhds, Tendsto.mono_left), g also tends from 𝓝[>] 0 to 𝓝 0.
   (b) For every s > 0, g(s) = ρ⁻¹·s > 0 (mul_pos with inv_pos.2 hρ). Hence g eventually lands in (0, ∞) along 𝓝[>] 0 (eventually_nhdsWithin_of_forall).
   (c) By tendsto_nhdsWithin_iff, (a) and (b) give Tendsto g (𝓝[>] 0) (𝓝[>] 0).

7. Limit. By part (B) of hQ applied to f, I tends to θ(x)·∫_Q f dμ along 𝓝[>] 0. Composing with Step 6 (Tendsto.comp), I ∘ g has the same limit along 𝓝[>] 0. By Step 5, (I ∘ g)(s) = J(M′, θ′, ρ • x, f)(s) for every s (Tendsto.congr). By Step 2, θ(x)·∫_Q f dμ = θ′(ρ • x)·∫_Q f dμ. Hence J(M′, θ′, ρ • x, f) tends to θ′(ρ • x)·∫_Q f dμ along 𝓝[>] 0.

8. Conclusion. Step 1 gives (A). Step 7, for arbitrary f ∈ C_c(ℝ^N, ℝ), gives (B) for (M′, θ′, ρ • x, Q). Therefore HasWeightedApproximateTangentSpaceAt k M′ θ′ (ρ • x) Q. ∎

Optional formalization aid (verified). The following declaration compiled in GMT/Ch06/Submission.lean position. That means after the contract definitions, inside namespace GMT.Ch06 with the contract's open commands, and needing no extra imports. Toolchain: Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308. #print axioms reports [propext, Classical.choice, Quot.sound].

theorem Submission.deformation_dilation_im_weightedTangent : ∀ (N k : ℕ) (ρ : ℝ) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (x : Eucl N) (Q : Submodule ℝ (Eucl N)), 0 < ρ → HasWeightedApproximateTangentSpaceAt k M θ x Q → HasWeightedApproximateTangentSpaceAt k ((fun y : Eucl N => ρ • y) '' M) (fun y : Eucl N => θ (ρ⁻¹ • y)) (ρ • x) Q := by
  intro N k ρ M θ x Q hρ hQ
  -- The new multiplicity at `ρ • x` is `θ x`.
  have hval : θ (ρ⁻¹ • ρ • x) = θ x := by rw [inv_smul_smul₀ hρ.ne']
  -- Blow-ups of `ρ M` at `ρ x` with ratio `s` are blow-ups of `M` at `x` with ratio `ρ⁻¹ s`.
  have hset : ∀ s : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap (ρ • x) s '' ((fun y : Eucl N => ρ • y) '' M) =
        Poincare.SimonGMT.Chapter03.blowUpMap x (ρ⁻¹ * s) '' M := by
    intro s
    rw [Set.image_image]
    refine Set.image_congr fun z _ => ?_
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
    rw [← smul_sub, smul_smul, mul_inv_rev, inv_inv]
  have hweight : ∀ (s : ℝ) (u : Eucl N),
      θ (ρ⁻¹ • (ρ • x + s • u)) = θ (x + (ρ⁻¹ * s) • u) := by
    intro s u
    rw [smul_add, inv_smul_smul₀ hρ.ne', smul_smul]
  -- `s ↦ ρ⁻¹ s` maps `𝓝[>] 0` to itself.
  have hlim : Tendsto (fun s : ℝ => ρ⁻¹ * s) (𝓝[>] 0) (𝓝[>] 0) := by
    have h0 : Tendsto (fun s : ℝ => ρ⁻¹ * s) (𝓝 0) (𝓝 (ρ⁻¹ * 0)) :=
      (continuous_const_mul ρ⁻¹).tendsto 0
    rw [mul_zero] at h0
    exact tendsto_nhdsWithin_iff.2 ⟨h0.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun s hs => mul_pos (inv_pos.2 hρ) hs⟩
  refine ⟨hQ.1, fun f => ?_⟩
  show Tendsto _ _ (𝓝 (θ (ρ⁻¹ • ρ • x) * _))
  rw [hval]
  refine ((hQ.2 f).comp hlim).congr fun s => ?_
  simp only [Function.comp_apply, hset, hweight]

## Key steps

1. finrank Q = k is inherited from the hypothesis.
2. θ′(ρ • x) = θ(ρ⁻¹ • ρ • x) = θ(x) (inv_smul_smul₀).
3. For every s, blowUpMap (ρ • x) s '' ρM = blowUpMap x (ρ⁻¹·s) '' M, since s⁻¹ • (ρ • z − ρ • x) = (s⁻¹·ρ) • (z − x) = (ρ⁻¹·s)⁻¹ • (z − x) (smul_sub, smul_smul, mul_inv_rev, inv_inv; valid also at s = 0).
4. θ′(ρ • x + s • u) = θ(x + (ρ⁻¹·s) • u) (smul_add, inv_smul_smul₀, smul_smul).
5. So the blow-up integral of (ρM, θ′) at ρ • x with ratio s equals I_f(ρ⁻¹·s), the blow-up integral of (M, θ) at x with ratio ρ⁻¹·s.
6. s ↦ ρ⁻¹·s tends from 𝓝[>] 0 to 𝓝[>] 0 (continuity at 0, positivity, tendsto_nhdsWithin_iff).
7. Compose the hypothesis limit with this reparametrization (Tendsto.comp, Tendsto.congr) and rewrite the limit value by step 2.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git rev-parse HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum + cmp of local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean, GMT/Ch06/Contract.lean, GMT/Ch06/Submission.lean (all ea3ee0dd…, byte-identical)`
- `grep -n -E '^(open|namespace|noncomputable section|section|end|variable|universe|set_option)' GMT/Ch06/Contract.lean (comparator replay scope; variable {P : ℕ} is not replayed)`
- `sed -n 25,50p;90,110p;320,345p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable:34, blowUpMap:96, HasWeightedApproximateTangentSpaceAt:330); grep -n '^(abbrev|def|structure)' Chapter06/Forms.lean Chapter06/Currents.lean (DifferentialForm and TestFormOn are abbrevs)`
- `grep -rn -E 'mem_inv_smul_set_iff₀|euclideanHausdorffMeasure_smul₀|aestronglyMeasurable_map_iff|setIntegral_image_emb|integrableOn_image\b|smulOfNeZero' mathlib/Mathlib, and grep -rn for restrict_image_emb|ae_map_iff|ae_smul_measure|dist_smul₀|image_sdiff|integral_smul_measure (all found: Bochner/Set.lean:576, IntegrableOn.lean:324, AEStronglyMeasurable.lean:668, MeasurePreserving.lean:86, Restrict.lean:887, Module.lean:191, ConstMulAction.lean:394, Volume/Measure.lean:152, MulAction.lean:153, Set/Image.lean:379, Bochner/Basic.lean:1052)`
- `python3 -I over dag.json: statuses and lean_statements of the root.deformation-a1.dilation-a1 children and the rescale-a1 children (ind_rs_* accepted); sibling types of calculus, hausdorff and integer_multiplicity asserted equal to the strings used; the three proposed names checked against all 619 lean_names and the raw text of dag.json and issue-workers.json (0 occurrences)`
- `grep -rl 'deformation_dilation_im_' runs/…/nodes/ (no match); git for-each-ref refs/heads refs/remotes | xargs git grep -l 'deformation_dilation_im_' -- GMT/Ch06/Submission.lean (no match)`
- `python3 over dag.json for split nodes with depends_on (e.g. local_to_global_im-a1, lattice_approximation-a1): no grandchild cites its parent's sibling dependency`
- `git show proof-workspace/…/rescale-a1-triple-image-a1-efeaf8ca5e:GMT/Ch06/Submission.lean and …/rescale-a1-tau-action-a1-c14ddccfbd:GMT/Ch06/Submission.lean (template proofs for y ↦ r⁻¹(y − x))`
- `python3 -I scripts/gen.py: lean_contract.validate_lean_statement + gmt-compare.child_modules(contract mode) for the parent and the three children -> Scratch/NC_<key>.lean`
- `lean Scratch/NC_parent.lean, NC_weighted_tangent.lean, NC_rectifiable_triple.lean, NC_tau_action.lean (LEAN_PATH from lake env; all EXIT=0, only the expected sorry warning)`
- `lean Scratch/Proto2.lean and Proto3.lean (three children and the hausdorff type proved, [propext, Classical.choice, Quot.sound]; parent compiles, with sorryAx only from the calculus stub; solution-side exact Submission.X checks pass); lean Scratch/Assembly.lean (dilation_im_assembly: [propext, Classical.choice, Quot.sound])`
- `sed -n 1455,1475p book/chapter-06.txt (5.3 scaled version: first changing scale, applying 5.1, then changing scale back)`
- `web search: Hausdorff measure scaling H^s(λA) = λ^s H^s(A) dilation (Imperial College M345PA46 ch. 2; McGill MATH 565 notes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1-integer-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1-integer-multiplicity-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/MulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Image.lean`
- `proof-workspace/gmt-ch06/20261011t144224z-6e4735dbca/theorems/solutions/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-triple-image-a1-efeaf8ca5e:GMT/Ch06/Submission.lean`
- `proof-workspace/gmt-ch06/20261011t144224z-6e4735dbca/theorems/solutions/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-tau-action-a1-c14ddccfbd:GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ddim-decomp-7c21/stmts.json`
- `/tmp/ddim-decomp-7c21/Scratch/NC_parent.lean`
- `/tmp/ddim-decomp-7c21/Scratch/NC_weighted_tangent.lean`
- `/tmp/ddim-decomp-7c21/Scratch/NC_rectifiable_triple.lean`
- `/tmp/ddim-decomp-7c21/Scratch/NC_tau_action.lean`
- `/tmp/ddim-decomp-7c21/Scratch/Proto2.lean`
- `/tmp/ddim-decomp-7c21/Scratch/Proto3.lean`
- `/tmp/ddim-decomp-7c21/Scratch/Assembly.lean`
- `/tmp/ddim-decomp-7c21/logs/NC_parent.log`
- `/tmp/ddim-decomp-7c21/logs/NC_weighted_tangent.log`
- `/tmp/ddim-decomp-7c21/logs/NC_rectifiable_triple.log`
- `/tmp/ddim-decomp-7c21/logs/NC_tau_action.log`
- `/tmp/ddim-decomp-7c21/logs/Proto2.log`
- `/tmp/ddim-decomp-7c21/logs/Proto3.log`
- `/tmp/ddim-decomp-7c21/logs/Assembly.log`

No project, SimonGMT or Mathlib declaration proves the selected statement or any proposed child. The accepted ind_rs_* lemmas on the rescale branch treat y ↦ r⁻¹(y − x), have different frozen types and live on another DAG branch, so they serve only as proof templates. The pinned Mathlib supplies everything needed: the measure-transport API (MeasurePreserving.setIntegral_image_emb, integrableOn_image, restrict_image_emb, MeasurableEmbedding.aestronglyMeasurable_map_iff and ae_map_iff, Measure.ae_smul_measure, Homeomorph.smulOfNeZero) plus Measure.euclideanHausdorffMeasure_smul₀, all inside the frozen import closure, so no import changes are needed. The snapshot Contract, the workspace Contract and Submission are byte-identical at the manifest commit. All three child statements validate, elaborate in the exact comparator scope, and have complete compiled proofs with [propext, Classical.choice, Quot.sound]; these are embedded verbatim in each child's proof. Their names are globally unused. Together with the resolved siblings calculus and hausdorff, they imply the selected frozen type with standard axioms only.
