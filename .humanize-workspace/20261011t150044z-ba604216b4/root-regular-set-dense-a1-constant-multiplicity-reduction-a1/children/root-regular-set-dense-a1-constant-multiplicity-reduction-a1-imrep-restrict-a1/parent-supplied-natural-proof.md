# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (R₀ := (M ∩ B, 1, ξ) is an IMRep in B; “T_x(M ∩ B) = Q because B is open: if spt f ⊆ B̄_R(0) and ρR < dist(x, ℝ^P ∖ B), then η_{x,ρ}(M ∩ B) and η_{x,ρ}(M) coincide on B̄_R(0), so the integrals in Definition 1.4 agree for small ρ”) and step 6(c) (R'_X := (M_X ∩ K, θ_X, ξ_X) is an IMRep in U; “H^n(M_X ∖ (M_X ∩ K)) = 0 and H^n(η_{x,ρ}(Z)) = ρ^{−n}H^n(Z), so the integrals in Definition 1.4 for M_X ∩ K and M_X coincide”). The two cases are unified by the local-null hypothesis. The splitting of ∫_{η_{x,λ}(M)} f dHⁿ is the one in Simon Ch. 3, proof of Theorem 1.6 “⇒”; the approximate tangent space is Simon Ch. 3, Definition 1.4 (HasApproximateTangentSpaceAt). Write Hⁿ = μHE[n] and η_λ(y) := λ⁻¹(y − x) (blowUpMap x λ).

Lemma A (tangent invariance). Let M' ⊆ M ⊆ ℝ^P be Borel sets, x ∈ ℝ^P, δ > 0 with Hⁿ((M ∖ M') ∩ B_δ(x)) = 0, and Q a subspace with HasApproximateTangentSpaceAt n M x Q. Then HasApproximateTangentSpaceAt n M' x Q.
Proof of Lemma A.
A1. The condition dim Q = n is part of the hypothesis.
A2. Fix f ∈ C_c(ℝ^P, ℝ). Its support is compact, so there is R₀ ≥ 0 with f(z) = 0 whenever |z| > R₀. For λ > 0 the map η_λ is an affine homeomorphism, so η_λ(M) and η_λ(M') are Borel; by injectivity η_λ(M) ∖ η_λ(M') = η_λ(M ∖ M').
A3. Let 0 < λ < δ/(R₀ + 1). If z ∈ η_λ(M ∖ M') and f(z) ≠ 0, then z = η_λ(y) with y ∈ M ∖ M' and |y − x| = λ|z| ≤ λR₀ < δ. Hence z ∈ Z_λ := η_λ((M ∖ M') ∩ B_δ(x)).
A4. Hⁿ(Z_λ) = 0. Indeed η_λ is the translation y ↦ y − x (an isometry, Isometry.euclideanHausdorffMeasure_image) followed by the dilation by λ⁻¹, so Hⁿ(η_λ(S)) = λ^{−n}Hⁿ(S) for every S (euclideanHausdorffMeasure_homothety_image); alternatively η_λ is λ⁻¹-Lipschitz, and Lipschitz images of Hⁿ-null sets are Hⁿ-null (LipschitzWith.hausdorffMeasure_image_le). Apply this with S = (M ∖ M') ∩ B_δ(x).
A5. By A3 and A4, Hⁿ-a.e. point of η_λ(M) ∖ η_λ(M') is a zero of f. Since η_λ(M') ⊆ η_λ(M) and η_λ(M) is measurable, ∫_{η_λ(M)} f dHⁿ = ∫_{η_λ(M')} f dHⁿ (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero; no integrability is needed).
A6. Thus λ ↦ ∫_{η_λ(M)} f dHⁿ and λ ↦ ∫_{η_λ(M')} f dHⁿ agree on (0, δ/(R₀ + 1)), a neighbourhood of 0 within (0, ∞). The first tends to ∫_Q f dHⁿ as λ ↓ 0, hence so does the second (Tendsto.congr'). As f was arbitrary, HasApproximateTangentSpaceAt n M' x Q.

Main proof. Define R' with carrier M ∩ A, multiplicity θ' and orientation ξ, and check the fields of IMRep U' n.
1. M ∩ A is Borel, because M is Borel (field of R) and A is Borel (hypothesis).
2. M ∩ A ⊆ U' by hypothesis.
3. M ∩ A is countably n-rectifiable, as a subset of M (CountablyRectifiable.mono).
4. θ' is measurable, and θ'(x) > 0 for x ∈ M ∩ A, by hypothesis.
5. For compact K ⊆ U', ∫_{(M∩A)∩K} θ' dHⁿ < ∞ by hypothesis.
6. ξ is a.e. strongly measurable for Hⁿ⌞(M ∩ A): it is so for Hⁿ⌞M (field of R), and Hⁿ⌞(M ∩ A) ≤ Hⁿ⌞M (Measure.restrict_mono; AEStronglyMeasurable.mono_measure).
7. Orientation. By the orients field of R, Hⁿ⌞M-a.e. x has a subspace Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ x) Q. As M ∩ A ⊆ M, this holds Hⁿ⌞(M ∩ A)-a.e. too (ae_restrict_of_ae_restrict_of_subset). By hypothesis, Hⁿ⌞(M ∩ A)-a.e. x also has δ > 0 with Hⁿ((M ∖ A) ∩ B_δ(x)) = 0. For x with both properties, Lemma A with M' = M ∩ A (so M ∖ M' = M ∖ A) gives HasApproximateTangentSpaceAt n (M ∩ A) x Q, and IsUnitOrientationOf (ξ x) Q is unchanged. So the orientation condition holds Hⁿ⌞(M ∩ A)-a.e.
8. By 1-7, R' is an IMRep in U'. By construction R'.carrier = M ∩ A, R'.mult = θ' and R'.orient = ξ. ∎

## Key steps

1. Lemma A: if Hⁿ((M ∖ M') ∩ B_δ(x)) = 0 then, for λ < δ/(R₀+1), the blow-ups η_{x,λ}(M) and η_{x,λ}(M') differ inside B̄_{R₀}(0) only by a Hⁿ-null set, so the integrals in Simon 3.1.4 agree and M' has the same approximate tangent space Q.
2. Borel measurability, rectifiability (subset), multiplicity measurability/positivity and local integrability of R' come from R or from the hypotheses.
3. Measurability of ξ and the a.e. orientation property pass from Hⁿ⌞M to Hⁿ⌞(M ∩ A); Lemma A at a.e. point converts T_xM to T_x(M ∩ A).

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
