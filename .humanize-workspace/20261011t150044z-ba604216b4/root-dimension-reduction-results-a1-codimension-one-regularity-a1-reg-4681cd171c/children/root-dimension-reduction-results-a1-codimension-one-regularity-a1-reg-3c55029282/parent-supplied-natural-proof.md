# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.lipschitz_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof, step 5 (Lipschitz graphs). It details the printed step of Simon Ch. 3, proof of 1.6 “⇐” (chapter-03.txt lines 247–256): “for any fixed x₀ ∈ E_j it is easy to check that (10), taken together with the extension theorem 1.2 of Ch. 2, implies E_j ∩ B_{δ/4}(x₀) ⊆ Q^T(graph f)”. Here the codimension is one: the graph is taken over the hyperplane v^⊥, and the extension is McShane's scalar extension (Ch. 2, 1.2; Mathlib `LipschitzOnWith.extend_real`). Departure (rigour only): closedness is obtained by taking Γ to be the coincidence set {z : τ̃(p(z)) = t(z)}, which is closed, and showing that it lies in the range of a Lipschitz map ℝ^m → E; the parent's identification of Γ with that range is not needed.

1. Coordinates. For z ∈ E put t(z) := ⟨z, v⟩ ∈ ℝ and p(z) := z − t(z)v. Since |v| = 1, ⟨p(z), v⟩ = t(z) − t(z)|v|² = 0, so p(z) ∈ P := (span{v})^⊥ = v^⊥, and z = p(z) + t(z)v. Both t and p are continuous (linear).

2. Two-point bound. Let x, x′ ∈ S and w := x′ − x. Then w = (p(x′) − p(x)) + (t(x′) − t(x))v, hence |w| ≤ |p(x′) − p(x)| + |t(x′) − t(x)| because |v| = 1. Also t(x′) − t(x) = ⟨w, v⟩, so the hypothesis gives |t(x′) − t(x)| ≤ ½|w| ≤ ½|p(x′) − p(x)| + ½|t(x′) − t(x)|, i.e. |t(x′) − t(x)| ≤ |p(x′) − p(x)|.

3. The height function. Define τ : E → ℝ by τ(y) := t(x_y), where x_y ∈ S is a chosen point with p(x_y) = y when y ∈ p(S), and x_y is arbitrary otherwise (e.g. Function.invFunOn p S). For x ∈ S the point x_{p(x)} ∈ S satisfies p(x_{p(x)}) = p(x), so step 2 gives |t(x_{p(x)}) − t(x)| ≤ 0, i.e. τ(p(x)) = t(x). By step 2 again, |τ(p(x)) − τ(p(x′))| = |t(x) − t(x′)| ≤ |p(x) − p(x′)| for x, x′ ∈ S, so τ is 1-Lipschitz on p(S) ⊆ E. By McShane's extension there is a 1-Lipschitz τ̃ : E → ℝ with τ̃ = τ on p(S); in particular τ̃(p(x)) = t(x) for every x ∈ S.

4. The closed set. Let Γ := {z ∈ E : τ̃(p(z)) = t(z)}. It is closed, being the set where two continuous functions agree, and S ⊆ Γ by step 3.

5. A Lipschitz parametrization. Since dim E = m + 1 and v ≠ 0, dim P = m, so there is a linear isometry ι of ℝ^m onto P (e.g. the inverse of the coordinate map of an orthonormal basis of P indexed by Fin m; Mathlib `OrthonormalBasis.fromOrthogonalSpanSingleton`). Define F : ℝ^m → E by F(y) := ι(y) + τ̃(ι(y))v. F is Lipschitz: y ↦ ι(y) and y ↦ τ̃(ι(y)) are 1-Lipschitz and s ↦ sv is 1-Lipschitz, so F is 2-Lipschitz.

6. Γ ⊆ range F. If z ∈ Γ, then p(z) ∈ P, so p(z) = ι(y) for y := ι^{-1}(p(z)), and F(y) = p(z) + τ̃(p(z))v = p(z) + t(z)v = z.

7. Conclusion. range F is countably m-rectifiable, being the range of one Lipschitz map ℝ^m → E (SimonGMT `countablyRectifiable_range`), hence so is its subset Γ (`CountablyRectifiable.mono`). Thus Γ is closed, countably m-rectifiable, and contains S. ∎

Lean note (non-normative aid). The following tactic proof of `Submission.codim1_rdo_dg_rc_closed_graph_cover` (the frozen type above, followed by `:= by`) compiles against the frozen contract: `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, Lean v4.35.0-rc3, Mathlib 25730c7c; `#print axioms` gives only propext, Classical.choice, Quot.sound.
```lean
  intro m v S hv hS
  -- Step 1: height `t` and orthogonal projection `p` onto `vᗮ`.
  obtain ⟨t, ht⟩ : ∃ t : Euclid (m + 1) → ℝ, ∀ z, t z = inner ℝ z v := ⟨_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Euclid (m + 1) → Euclid (m + 1), ∀ z, p z = z - t z • v :=
    ⟨_, fun _ => rfl⟩
  have hvv : inner ℝ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hpv : ∀ z, inner ℝ (p z) v = (0 : ℝ) := by
    intro z
    rw [hp, inner_sub_left, real_inner_smul_left, hvv, ht, mul_one, sub_self]
  have hpmem : ∀ z, p z ∈ (ℝ ∙ v)ᗮ := by
    intro z
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hpv z
  have hdecomp : ∀ z, p z + t z • v = z := by
    intro z
    rw [hp, sub_add_cancel]
  -- Step 2: the key inequality `|t x' - t x| ≤ ‖p x' - p x‖` on `S`.
  have key : ∀ x ∈ S, ∀ x' ∈ S, |t x' - t x| ≤ ‖p x' - p x‖ := by
    intro x hx x' hx'
    have h1 := hS x hx x' hx'
    have h2 : inner ℝ (x' - x) v = t x' - t x := by
      rw [inner_sub_left, ht, ht]
    have h3 : x' - x = (p x' - p x) + (t x' - t x) • v := by
      rw [hp, hp, sub_smul]
      abel
    have h4 : ‖x' - x‖ ≤ ‖p x' - p x‖ + |t x' - t x| := by
      calc ‖x' - x‖ = ‖(p x' - p x) + (t x' - t x) • v‖ := by rw [← h3]
        _ ≤ ‖p x' - p x‖ + ‖(t x' - t x) • v‖ := norm_add_le _ _
        _ = ‖p x' - p x‖ + |t x' - t x| := by
          rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
    rw [h2] at h1
    linarith
  -- Step 3: the height as a function of the projection, and its McShane extension.
  obtain ⟨τ, hτ⟩ : ∃ τ : Euclid (m + 1) → ℝ, ∀ x ∈ S, τ (p x) = t x := by
    refine ⟨fun y => t (Function.invFunOn p S y), ?_⟩
    intro x hx
    have hex : ∃ a ∈ S, p a = p x := ⟨x, hx, rfl⟩
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have h := key x hx _ hmem
    rw [heq, sub_self, norm_zero] at h
    have h0 : t (Function.invFunOn p S (p x)) - t x = 0 := abs_nonpos_iff.mp h
    show t (Function.invFunOn p S (p x)) = t x
    linarith
  have hτLip : LipschitzOnWith 1 τ (p '' S) := by
    apply LipschitzOnWith.mk_one
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [hτ x hx, hτ x' hx', Real.dist_eq, dist_eq_norm]
    exact key x' hx' x hx
  obtain ⟨τ', hτ'Lip, hτ'eq⟩ := hτLip.extend_real
  -- Step 4: an isometry `ι : ℝᵐ ≃ vᗮ` and the Lipschitz graph map `F`.
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hv0 : v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  let ι := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m hv0).repr.symm
  let F : Euclid m → Euclid (m + 1) := fun y => ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1)) +
    τ' ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1)) • v
  have hFLip : ∃ K, LipschitzWith K F := by
    have h1 : LipschitzWith (1 * 1)
        (fun y : Euclid m => ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1))) :=
      (Submodule.subtypeₗᵢ (ℝ ∙ v)ᗮ).lipschitzWith.comp ι.lipschitzWith
    have hsm : LipschitzWith 1 (fun r : ℝ => r • v) := by
      apply LipschitzWith.mk_one
      intro r s
      rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq, Real.norm_eq_abs]
    exact ⟨_, h1.add (hsm.comp (hτ'Lip.comp h1))⟩
  obtain ⟨K, hK⟩ := hFLip
  -- Step 5: the closed graph `Γ = {z | τ' (p z) = t z}`.
  have htc : Continuous t := by
    rw [show t = fun z => inner ℝ z v from funext ht]
    fun_prop
  have hpc : Continuous p := by
    rw [show p = fun z => z - t z • v from funext hp]
    fun_prop
  refine ⟨{z | τ' (p z) = t z}, ?_, ?_, ?_⟩
  · exact isClosed_eq (hτ'Lip.continuous.comp hpc) htc
  · apply (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hK).mono
    intro z hz
    simp only [mem_ofPred_eq] at hz
    refine ⟨ι.symm ⟨p z, hpmem z⟩, ?_⟩
    simp only [F, LinearIsometryEquiv.apply_symm_apply]
    rw [hz]
    exact hdecomp z
  · intro x hx
    simp only [mem_ofPred_eq]
    rw [← hτ'eq (mem_image_of_mem p hx)]
    exact hτ x hx
```

## Key steps

1. Split z = p(z) + t(z)v with t(z) = ⟨z, v⟩ and p(z) ∈ v^⊥.
2. The hypothesis gives |t(x′) − t(x)| ≤ |p(x′) − p(x)| on S, so τ(p(x)) := t(x) is a well-defined 1-Lipschitz function on p(S).
3. McShane extends τ to a 1-Lipschitz τ̃ on E; Γ := {z : τ̃(p(z)) = t(z)} is closed and contains S.
4. Γ lies in the range of the Lipschitz map F(y) = ι(y) + τ̃(ι(y))v (ι : ℝ^m → v^⊥ an onto isometry), so Γ is countably m-rectifiable.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: selected node (depth 5, no children), sibling flat_tangent_density frozen type, collision check of the 7 codim1_rdo_dg_rc_* names, statements mentioning CountablyRectifiable or 16 ^ (cbrr_*, dpf*, codim1_rdo_*)`
- `rg -n 'theorem measurable_measure_prodMk_left|theorem LipschitzOnWith.extend_real|isClosed_range|finite_cover_balls|exists_isCompact_diff_lt|orthogonal_span_singleton|fromOrthogonalSpanSingleton|isOpen_biUnion_countable|isOpen_iUnion_countable|tendsto_measure_iUnion_atTop|Measurable.inner|instance.*InnerRegularCompactLTTop' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 100,280p book/chapter-03.txt (printed proof of Simon Ch. 3, 1.6 ⇐)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Names.lean and Names2.lean (#check of the lemmas above inside the import closure of GMT.Ch07.Submission)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Types.lean, Assembly.lean, Full.lean and /tmp/rc-final/Verify.lean (7 child types, child proofs rebuilt from the returned JSON, parent assembly with a sorry stub of the uncle; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4681cd171c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rc-split-check/Full.lean`
- `/tmp/rc-final/Verify.lean`

Pins: the snapshot manifest pins project b4d606db and Mathlib 25730c7c, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503aa28…).

No local declaration states any of the seven children. SimonGMT Chapter03/Rectifiable.lean supplies only the definition CountablyRectifiable and the lemmas countablyRectifiable_range, _iUnion, _sUnion, _of_measure_zero and CountablyRectifiable.mono, which the children use. The related general-codimension DAG branch (cbr_rectifiable_of_approx_tangent → cbrr_cone_claim, cbrr_rectifiable_of_uniform_density) is unaccepted and has different types, so nothing is reused.

Snapshot Mathlib supplies:
- measurable_measure_prodMk_left (Prod.lean:97);
- LipschitzOnWith.extend_real (Lipschitz.lean:308);
- AntilipschitzWith.isClosed_range (Antilipschitz.lean:175);
- OrthonormalBasis.fromOrthogonalSpanSingleton (PiL2.lean:1157);
- MeasurableSet.exists_isCompact_sdiff_lt (Regular.lean:843), with an InnerRegularCompactLTTop instance for every measure on Euclid (RegularityCompacts.lean:186);
- tendsto_measure_iUnion_atTop (Continuity.lean:198);
- IsCompact.finite_cover_balls (Pseudo/Basic.lean:260);
- TopologicalSpace.isOpen_biUnion_countable.
Measurable.inner (SpecialFunctions/Inner.lean) is outside the import closure, so Continuous.measurable2 is used instead.

Lean: all 7 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens. Every child is proved with axioms propext, Classical.choice, Quot.sound only. The selected frozen type is proved from halving_step, of_halving and a sorry stub of the uncle Submission.codim1_rdo_dg_flat_tangent_density_cone; the only extra axiom is sorryAx, from that stub.

Names: the 7 codim1_rdo_dg_rc_* identifiers occur nowhere in dag.json (945 nodes), GMT/, SimonGMT or Mathlib.
