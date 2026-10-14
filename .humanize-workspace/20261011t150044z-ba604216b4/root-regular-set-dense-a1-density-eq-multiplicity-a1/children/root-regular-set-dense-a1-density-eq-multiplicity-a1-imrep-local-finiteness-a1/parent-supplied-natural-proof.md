# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1`
- Child DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1.imrep_local_finiteness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (Local finiteness) of the parent proof. This is the standing hypothesis of Simon Ch. 6, Definition 3.1 (chapter-06.txt lines 733-747): the multiplicity θ is a locally H^n-integrable positive integer-valued function. In the frozen contract it is encoded by the IMRep fields mult_pos and locallyIntegrable_mult.

Notation: H^n = μHE[n] on ℝ^P (Euclid P); M = R.carrier; θ(x) = R.mult x ∈ ℕ ⊆ [0, ∞]; μ_R = R.measure = (H^n⌞M).withDensity θ. Fix a compact K ⊆ ℝ^P with K ⊆ U.

1. K is a compact subset of the Hausdorff space ℝ^P, hence closed, hence Borel (IsCompact.measurableSet).

2. (Weight of K.) Since K is measurable:
- μ_R(K) = ∫_K θ d(H^n⌞M) by the definition of withDensity (withDensity_apply);
- (H^n⌞M)⌞K = H^n⌞(K ∩ M) (Measure.restrict_restrict).
Hence μ_R(K) = ∫_{M∩K} θ dH^n, after commuting the intersection.

3. The IMRep field locallyIntegrable_mult, applied to the compact set K ⊆ U, gives ∫_{M∩K} θ dH^n ≠ ∞. By step 2, μ_R(K) ≠ ∞. This is the second conclusion.

4. (θ ≥ 1 on M.) For x ∈ M ∩ K, the field mult_pos gives 0 < R.mult x in ℕ. Hence 1 ≤ R.mult x, and after casting to [0, ∞], 1 ≤ θ(x).

5. (Measurability.) θ is measurable. It is the composition of the measurable map R.mult : ℝ^P → ℕ (field measurable_mult) with the cast ℕ → [0, ∞], and every map out of the discrete space ℕ is measurable (measurable_from_nat).

6. (Unweighted measure.) H^n(M ∩ K) = ∫_{M∩K} 1 dH^n (setLIntegral_one). This is at most ∫_{M∩K} θ dH^n by monotonicity of the set lower integral (setLIntegral_mono), using the pointwise bound of step 4 on M ∩ K and the measurability of step 5. The right side is finite by step 3, so H^n(M ∩ K) ≠ ∞. This is the first conclusion. ∎

Appendix (verified Lean realization of the numbered proof above). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c. It was placed after `import GMT.Ch07.Submission` in the child comparator scope, i.e. inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after the contract's `noncomputable section ... end`. `exact Submission.rsd_imrep_compact_measure_ne_top` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
```

## Key steps

1. A compact K is closed, hence Borel.
2. μ_R(K) = ∫_{M∩K} θ dH^n by withDensity_apply and restrict_restrict. This is finite by locallyIntegrable_mult.
3. θ ≥ 1 on M (mult_pos) gives H^n(M ∩ K) = ∫_{M∩K} 1 dH^n ≤ ∫_{M∩K} θ dH^n < ∞.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem ae_tendsto_rnDeriv|theorem rnDeriv_withDensity\b|theorem restrict_withDensity\b|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_image|theorem addHaar_closedBall\b|theorem addHaar_ball\b|theorem integral_indicator_one' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'theorem\|lemma\|def \|notation\|instance' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'HasApproximateTangentSpaceAt\|^def \|^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; rg -n 'def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n -t lean 'HasApproximateTangentSpaceAt' simongmt/Poincare; rg -n -t lean 'theorem [A-Za-z_.]*(density|Density)[A-Za-z_.]*' simongmt/Poincare/SimonGMT/Chapter03 simongmt/Poincare/SimonGMT/Chapter04`
- `rg -n -t lean 'theorem .*IMRep|IMRep\.measure.*≠ ∞|locallyIntegrable_mult' local-references/123e8435b4a2469b/project`
- `python3 -I scan of dag.json lean_statement fields for closedBall|HasApproximateTangentSpaceAt|withDensity|unitBallVolume (overlap check with other DAG nodes)`
- `grep -l '<four proposed names>' dag.json issue-workers.json DAG.md GMT/Ch07/*.lean; rg -l -t lean '<four proposed names>' simongmt GMT local-references/123e8435b4a2469b/project; git grep -l -E '<four proposed names>' over all 101 refs -- GMT`
- `sed -n 500,595p verifier/gmt-compare.py (contract_scope / child_modules: child statements elaborate after import GMT.Ch07.Submission with the replayed contract opens)`
- `lake env lean /tmp/dem-split/Children.lean (four child types elaborate in the replayed comparator scope)`
- `lake env lean /tmp/dem-split/ChildAFacts.lean (Hn(Q ∩ B̄_r(0)) = unitBallVolume n * r^n and Hn(blowUpMap x r '' A) = r^-n Hn(A))`
- `lake env lean /tmp/dem-split/AllChildren.lean (full proofs of the four children, exact-type checks `exact Submission.<name>`, conditional assembly of the selected type from the children plus rsd_massOn_eq_measure as hypothesis; #print axioms)`
- `lake env lean /tmp/dem-split/out/Solo_<name>.lean for each of the four children (standalone compilation, #print axioms)`
- `book: sed -n 77,101p chapter-03.txt; sed -n 280,325p chapter-03.txt; sed -n 561,592p chapter-01.txt; sed -n 760,975p chapter-01.txt; sed -n 730,770p chapter-06.txt; sed -n 335,360p chapter-04.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1/parent-supplied-natural-proof.md`
- `/tmp/dem-split/Children.lean`
- `/tmp/dem-split/Assembly.lean`
- `/tmp/dem-split/ChildAFacts.lean`
- `/tmp/dem-split/ChildA.lean`
- `/tmp/dem-split/ChildB.lean`
- `/tmp/dem-split/ChildC.lean`
- `/tmp/dem-split/ChildD.lean`
- `/tmp/dem-split/AllChildren.lean`
- `/tmp/dem-split/out/Solo_rsd_tendsto_closedBall_density_of_approxTangent.lean`
- `/tmp/dem-split/out/Solo_rsd_ae_tendsto_withDensity_div_closedBall.lean`
- `/tmp/dem-split/out/Solo_rsd_tendsto_ball_density_of_closedBall.lean`
- `/tmp/dem-split/out/Solo_rsd_imrep_compact_measure_ne_top.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No ready-made lemma exists in the Ch07 environment for any of the four child facts:
- the project has only the IMRep structure fields (e.g. locallyIntegrable_mult) and no IMRep local-finiteness lemma;
- there is no open/closed-ball density transfer lemma and no localized Besicovitch statement;
- simongmt Chapter04/TangentDensity.lean has related lemmas (hausdorff_blowUp_image, blowUp_image_inter_closedBall, one_le_density_of_approximateTangent). They concern simongmt varifold weights, give only the lower bound d ≥ 1, and Chapter04 is not imported by the Ch07 contract, so they are not reused.

Library facts reused, located in the snapshot and exercised in compiled proofs:
- Besicovitch.ae_tendsto_rnDeriv (Covering/Besicovitch.lean:1078), Measure.rnDeriv_withDensity (Decomposition/Lebesgue.lean:591), restrict_withDensity (WithDensity.lean:215);
- Measure.addHaar_closedBall (Lebesgue/EqHaar.lean:500), integral_indicator_one (Bochner/Set.lean:533);
- in Geometry/Euclidean/Volume/Measure.lean: Isometry.euclideanHausdorffMeasure_image (line 131), Measure.euclideanHausdorffMeasure_smul₀ (line 152), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (line 187);
- simongmt HasApproximateTangentSpaceAt (Rectifiable.lean:102) and blowUpMap (Rectifiable.lean:96).

Verification:
- All four child types elaborate in the comparator scope, i.e. import GMT.Ch07.Submission plus the replayed contract opens (verifier/gmt-compare.py, contract_scope).
- Full Lean proofs of all four children compile standalone with exact Submission.<name> type checks.
- The conditional assembly of the selected frozen type from the four children plus rsd_massOn_eq_measure compiles.
- #print axioms reports only propext, Classical.choice and Quot.sound in every case.

The four names occur nowhere in dag.json, issue-workers.json, DAG.md, GMT/, the simongmt sources, the snapshot project, or any of the 101 git refs, so they collide with no reserved declaration.
