# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.constant_mult_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (“R₀ := (M ∩ B, 1, ξ) is an IMRep in B … T₀(ω) = N₀^{−1}∫_M θ⟨ω, ξ⟩ dH^n = N₀^{−1}∫_{M∩B} N₀⟨ω, ξ⟩ dH^n = ∫_{M∩B} 1·⟨ω, ξ⟩ dH^n”), with B replaced by an arbitrary open V ⊆ U; Simon Ch. 5, proof of Corollary 7.3 (Ṽ = v(M, N^{−1}θ)⌞B_ρ(ξ)). Uses the sibling imrep_restrict (Submission.rsd_cmr_imrep_restrict). Write Hⁿ = μHE[n].

1. From μ_T-a.e. to Hⁿ⌞M-a.e. R.measure is (Hⁿ⌞M).withDensity θ with θ measurable. A property holds a.e. for this measure iff it holds Hⁿ⌞M-a.e. at the points where θ ≠ 0 (ae_withDensity_iff). Hⁿ⌞M-a.e. x lies in M (ae_restrict_mem), and θ(x) ≥ 1 there (mult_pos). Hence Hⁿ⌞M-a.e. x satisfies: x ∈ V ⇒ θ(x) = N₀. As M is Borel (ae_restrict_iff'), equivalently Hⁿ-a.e. x satisfies: x ∈ M ∩ V ⇒ θ(x) = N₀.

2. The triple (M ∩ V, 1, ξ). Apply imrep_restrict to R with A := V, U' := V and θ' :≡ 1:
 (a) V is Borel (open), and M ∩ V ⊆ V;
 (b) the constant 1 is measurable and positive;
 (c) for compact K ⊆ V: ∫_{M∩V∩K} 1 dHⁿ ≤ ∫_{M∩V∩K} θ dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞, using θ ≥ 1 on M (setLIntegral_mono), monotonicity in the set (lintegral_mono_set), and locallyIntegrable_mult of R (K ⊆ V ⊆ U);
 (d) every x ∈ M ∩ V has δ > 0 with B_δ(x) ⊆ V (V open), so (M ∖ V) ∩ B_δ(x) = ∅ has Hⁿ-measure 0; in particular the local-null condition holds Hⁿ⌞(M ∩ V)-a.e.
 This gives an IMRep R₀ in V with R₀.carrier = M ∩ V, R₀.mult = 1 and R₀.orient = ξ.

3. Representation. Let ω ∈ 𝒟^n(V); ι ω has the same underlying form ω. By R.Represents T and the hypothesis,
 N₀·T₀(ω) = T(ι ω) = ∫_M θ(x)ξ(x)(ω(x)) dHⁿ(x).
 (a) For x ∈ M ∖ V we have x ∉ tsupport ω (tsupport ω ⊆ V), so ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and the integrand θ(x)ξ(x)(0) = 0. Hence ∫_M θ ξ(ω) dHⁿ = ∫_{M∩V} θ ξ(ω) dHⁿ (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, M Borel).
 (b) By step 1, θ ξ(ω) = N₀ ξ(ω) Hⁿ-a.e. on M ∩ V. So ∫_{M∩V} θ ξ(ω) dHⁿ = ∫_{M∩V} N₀ ξ(ω) dHⁿ = N₀ ∫_{M∩V} ξ(ω) dHⁿ (setIntegral_congr_ae, integral_const_mul; neither needs integrability).
 (c) Hence N₀·T₀(ω) = N₀·∫_{M∩V} ξ(ω) dHⁿ, and since N₀ ≠ 0, T₀(ω) = ∫_{M∩V} 1·ξ(x)(ω(x)) dHⁿ(x) = R₀.action ω.

4. So R₀.Represents T₀, and T₀ is integer multiplicity in V. ∎

## Key steps

1. ae_withDensity_iff and θ ≥ 1 on M turn 'θ = N₀ μ_T-a.e. on V' into 'θ = N₀ Hⁿ-a.e. on M ∩ V'.
2. imrep_restrict with A = U' = V and multiplicity 1 gives the IMRep (M ∩ V, 1, ξ) in V (local integrability from θ ≥ 1; local-null condition trivial because V is open).
3. N₀T₀(ω) = ∫_M θξ(ω) = ∫_{M∩V} θξ(ω) = N₀∫_{M∩V} ξ(ω) (ω = 0 off V; θ = N₀ a.e. on M ∩ V); cancel N₀.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 over dag.json: lean_name/lean_statement of all 111 nodes; frozen statements of rsd_massOn_eq_measure, rsd_mem_support_iff_measure_ball_pos, rsd_isIntegerMultiplicity_int_combination and of the selected node; rg -l rsd_cmr_ over the run directory and GMT/`
- `python3 over nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1/decomposition-v1.json (convention: children do not use the parent's resolved siblings)`
- `rg -n 'restrictDomain|zeroRegion|VanishesOn|theorem .*massOn|theorem .*support' simongmt/Poincare/SimonGMT (Chapter06)`
- `sed simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean and Chapter03/Rectifiable.lean (HasApproximateTangentSpaceAt, blowUpMap, CountablyRectifiable.mono)`
- `grep/rg in local-references/123e8435b4a2469b/mathlib: exists_contDiff_support_eq_eq_one_iff, IsCompact.exists_cthickening_subset_open, measure_null_of_locally_null, ae_withDensity_iff, setIntegral_eq_of_subset_of_*, euclideanHausdorffMeasure_homothety_image, LipschitzWith.hausdorffMeasure_image_le, ENNReal.mul_sSup`
- `lake env lean /tmp/rsd-cmr-decomp/build/FinalChildren.lean, FinalAssembly.lean, FinalSiblings.lean, FinalLeaves.lean (#print axioms)`
- `book: chapter-05.txt proof of 7.3; chapter-06.txt 2.11, 2.16, 3.1, 3.2; chapter-03.txt 1.4-1.6`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rsd-cmr-decomp/build/FinalChildren.lean`
- `/tmp/rsd-cmr-decomp/build/FinalAssembly.lean`
- `/tmp/rsd-cmr-decomp/build/FinalSiblings.lean`
- `/tmp/rsd-cmr-decomp/build/FinalLeaves.lean`

The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

The pinned library proves none of the children:
- Chapter06 has restrictDomain, testFormOnInclusion, zeroRegion/support, massOn_mono and le_massOn, but no mass or support lemma for restricted or scaled currents.
- Currents.lean explicitly leaves the integral continuity estimate (IMRep action as a current) open.
- Chapter03 has HasApproximateTangentSpaceAt and CountablyRectifiable.mono, but no locality or null-set invariance of approximate tangent spaces.

Reusable tools, all used in compiled proofs:
- Mathlib: exists_contDiff_support_eq_eq_one_iff, IsCompact.exists_cthickening_subset_open, measure_null_of_locally_null, ae_withDensity_iff, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_congr_set/_ae, ENNReal.mul_sSup.
- The muHE scaling and isometry lemmas are cited for imrep_restrict.

Lean checks:
- All nine child types elaborate in the comparator scope.
- The conditional assembly of the exact frozen parent type from seven children plus the three frozen uncle types depends only on propext, Classical.choice and Quot.sound.
- Both sibling dependencies are verified.
- Five leaf children are fully proved.

No rsd_cmr_ name collides with the 111 live DAG declarations.
