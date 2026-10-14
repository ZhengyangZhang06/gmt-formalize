# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.ball_cone_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof, step 2(a) (“G_k is Borel”), which supplies the measurability that Simon's printed proof of 1.6 “⇐” leaves unaddressed (chapter-03.txt lines 192–203: the functions f_k, q_k fed to Egoroff's theorem). Departure (rigour/convenience only): instead of the parent's upper-semicontinuity/reverse-Fatou argument, which needs μ finite, measurability is obtained from the section lemma of Tonelli's theorem, valid for every s-finite μ. The conclusion is the same and is exactly what step 2(a) uses.

1. E × E carries the product σ-algebra, which coincides with its Borel σ-algebra because E is second countable. Hence continuous maps on E × E are measurable, and so are compositions of continuous maps with measurable maps. In particular (x, z) ↦ |z − x| and (x, z) ↦ α|z − x| are measurable, and so is (x, z) ↦ (z − x, ν(x)) ∈ E × E, because ν is Borel and the two projections are measurable.

2. Let A := {(x, z) ∈ E × E : |z − x| ≤ q}. It is closed (the preimage of (−∞, q] under the continuous map (x, z) ↦ |z − x|), hence measurable, and for each x its section {z : (x, z) ∈ A} equals B̄_q(x).

3. Let B := {(x, z) ∈ E × E : α|z − x| ≤ |⟨z − x, ν(x)⟩|}. The map (x, z) ↦ |⟨z − x, ν(x)⟩| is measurable as the composition of the continuous map (a, b) ↦ |⟨a, b⟩| on E × E with the measurable map (x, z) ↦ (z − x, ν(x)); the map (x, z) ↦ α|z − x| is continuous. The set where one measurable real function is ≤ another is measurable, so B is measurable, and so is B ∩ A, whose x-section is {z : α|z − x| ≤ |⟨z − x, ν(x)⟩|} ∩ B̄_q(x).

4. For an s-finite measure μ on E and a measurable S ⊆ E × E, the function x ↦ μ({z : (x, z) ∈ S}) is measurable (the measurability part of Tonelli's theorem; Mathlib `measurable_measure_prodMk_left`). Applying this to S := A and to S := B ∩ A and using the section identities of steps 2 and 3 gives both claims. ∎

Lean note (non-normative aid). The following tactic proof of `Submission.codim1_rdo_dg_rc_ball_cone_measurable` (the frozen type above, followed by `:= by`) compiles against the frozen contract: `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, Lean v4.35.0-rc3, Mathlib 25730c7c; `#print axioms` gives only propext, Classical.choice, Quot.sound.
```lean
  intro m μ ν α q hμ hν
  have hA : MeasurableSet {p : Euclid (m + 1) × Euclid (m + 1) | dist p.2 p.1 ≤ q} :=
    measurableSet_le (continuous_dist.comp (continuous_snd.prodMk continuous_fst)).measurable
      measurable_const
  have hB : MeasurableSet {p : Euclid (m + 1) × Euclid (m + 1) |
      α * ‖p.2 - p.1‖ ≤ |inner ℝ (p.2 - p.1) (ν p.1)|} := by
    refine measurableSet_le ?_ ?_
    · exact (continuous_const.mul (continuous_norm.comp
        (continuous_snd.sub continuous_fst))).measurable
    · exact continuous_abs.measurable.comp (Continuous.measurable2 continuous_inner
        (measurable_snd.sub measurable_fst) (hν.comp measurable_fst))
  refine ⟨?_, ?_⟩
  · have h := measurable_measure_prodMk_left (ν := μ) hA
    convert h using 2 with x
    rfl
  · have h := measurable_measure_prodMk_left (ν := μ) (hB.inter hA)
    convert h using 2 with x
    rfl
```

## Key steps

1. The closed set A = {(x, z) : |z − x| ≤ q} ⊆ E × E has x-sections B̄_q(x).
2. B = {(x, z) : α|z − x| ≤ |⟨z − x, ν(x)⟩|} is measurable because ν is Borel; B ∩ A has the cone-ball sections.
3. For s-finite μ, x ↦ μ(S_x) is measurable for every measurable S ⊆ E × E (Tonelli section lemma).

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
