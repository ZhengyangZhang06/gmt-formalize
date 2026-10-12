# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_density_infinite-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_density_infinite-a1.plane_ball_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the part of fact (F2) of the parent proof used in steps 5–6 (ω < ∞ and the scaling formula; positivity of ω is not needed), isolated: Simon, Introduction to GMT, Ch. 1, Theorem 2.9 (printed p. 11; book/chapter-01.txt lines 445–470: Lⁿ = Hⁿ on ℝⁿ), combined with the invariance of Hausdorff measure under isometries and the scaling of Lebesgue measure under dilations. Mathlib packages these facts as MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure (Mathlib/Geometry/Euclidean/Volume/Measure.lean:104: μHE[finrank V] is an additive Haar measure on every finite-dimensional real normed space V with its Borel σ-algebra), Isometry.euclideanHausdorffMeasure_image (same file, line 131: μHE[d](f '' s) = μHE[d](s) for an isometry f) and Measure.addHaar_closedBall' (Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:475: μ(closedBall x r) = ofReal(r^(finrank)) · μ(closedBall 0 1) for an additive Haar measure μ and r ≥ 0).

Notation. Hⁿ := μHE[n] on ℝ^N. Let V be W regarded as a type (the subtype {x // x ∈ W}) with the induced norm, inner product and metric and the induced σ-algebra, which is the Borel σ-algebra of V because ℝ^N carries its Borel σ-algebra (Mathlib Subtype.borelSpace). Let j : V → ℝ^N, j(v) = v, be the inclusion; for z ∈ V and r ∈ ℝ let B̄_V(z, r) := {v ∈ V : dist(v, z) ≤ r}; let μ := μHE[n] computed intrinsically on V; and ω := Hⁿ(W ∩ B̄(0, 1)).

1. Since dim W = n we may replace n by finrank_ℝ V everywhere (in Lean: subst the hypothesis finrank ℝ W = n). V is a finite-dimensional real inner product space, hence a proper metric space: every closed ball B̄_V(z, r) is compact.

2. μ = μHE[finrank V] on V is an additive Haar measure on V (Mathlib isAddHaarMeasure_euclideanHausdorffMeasure; mathematically, Simon 1.2.9 transported to V by a linear isometry ℝⁿ ≅ V). Consequently (a) μ is finite on compact sets, and (b) for every z ∈ V and r ≥ 0, μ(B̄_V(z, r)) = ofReal(rⁿ) · μ(B̄_V(0, 1)) (Mathlib Measure.addHaar_closedBall').

3. For z ∈ V and r ∈ ℝ, W ∩ B̄(j z, r) = j(B̄_V(z, r)). Indeed the metric of V is the restriction of that of ℝ^N: dist(v, z) = |j v − j z| (Subtype.dist_eq). If v ∈ B̄_V(z, r), then j v ∈ W and |j v − j z| ≤ r, so j v ∈ W ∩ B̄(j z, r). Conversely, if x ∈ W ∩ B̄(j z, r), then v := ⟨x, x ∈ W⟩ ∈ V satisfies dist(v, z) = |x − j z| ≤ r and j v = x.

4. j is an isometry (Mathlib isometry_subtype_coe), hence Hⁿ(j(E)) = μHE[n](E) = μ(E) for every E ⊆ V (Mathlib Isometry.euclideanHausdorffMeasure_image). With 3: Hⁿ(W ∩ B̄(j z, r)) = μ(B̄_V(z, r)) for all z ∈ V, r ∈ ℝ. Taking z = 0 (note j 0 = 0) and r = 1 gives ω = μ(B̄_V(0, 1)).

5. Finiteness. B̄_V(0, 1) is compact by 1 and μ is finite on compact sets by 2(a); hence ω = μ(B̄_V(0, 1)) < ∞.

6. Scaling. Let y ∈ W and ρ ≥ 0, and put z := ⟨y, y ∈ W⟩ ∈ V, so that j z = y. By 4, 2(b) and 4 again,
 Hⁿ(W ∩ B̄(y, ρ)) = μ(B̄_V(z, ρ)) = ofReal(ρⁿ) · μ(B̄_V(0, 1)) = ofReal(ρⁿ) · ω.
Together with 5 this proves both conjuncts of the statement: μHE[n] (W ∩ closedBall 0 1) < ∞, and μHE[n] (W ∩ closedBall y ρ) = ENNReal.ofReal (ρ ^ n) * μHE[n] (W ∩ closedBall 0 1) for all y ∈ W and ρ ≥ 0. ∎

## Key steps

1. Regard W as the n-dimensional inner product space V (subtype, Borel σ-algebra); with n = finrank V, μHE[n] on V is an additive Haar measure (isAddHaarMeasure_euclideanHausdorffMeasure).
2. The inclusion V → ℝ^N is an isometry mapping the closed ball B̄_V(z, r) onto W ∩ B̄(z, r), so Hⁿ(W ∩ B̄(z, r)) = μHE[n]_V(B̄_V(z, r)) (Isometry.euclideanHausdorffMeasure_image).
3. A Haar measure is finite on the compact ball B̄_V(0, 1) and satisfies μ(B̄_V(z, ρ)) = ofReal(ρⁿ) μ(B̄_V(0, 1)) (Measure.addHaar_closedBall').
4. Hence ω = μ(B̄_V(0,1)) < ∞ and Hⁿ(W ∩ B̄(y, ρ)) = ofReal(ρⁿ) ω for y ∈ W, ρ ≥ 0.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "theorem exists_disjoint_covering_ae\b" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "theorem addHaar_closedBall'" mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n "instance MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure|theorem Isometry.euclideanHausdorffMeasure_image|theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "starProjection_apply_mem" mathlib/Mathlib/Analysis/InnerProductSpace/`
- `rg -n "^theorem measure_biUnion |^theorem measure_biUnion_le" mathlib/Mathlib/MeasureTheory`
- `rg -n "protected theorem Tendsto.const_div|theorem tendsto_ofReal_atTop" mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `rg -n -i "vitali|closedBall" project/GMT/Ch03/Contract.lean`
- `rg -n "^import" project/GMT/Ch03/Submission.lean`
- `rg -l -i "vitali" simongmt/Poincare/SimonGMT`
- `rg -n "Submodule.*closedBall|closedBall.*Submodule" simongmt/Poincare/SimonGMT`
- `rg -n "addHaar_closedBall|exists_disjoint_covering_ae" simongmt/Poincare/SimonGMT`
- `rg -c "bf_plane" dag.json; rg -l "bf_plane" nodes/ (lean_name collision check)`
- `lake env lean GMT/Scratch/ConeDensityInfiniteSplitDecision.lean (import GMT.Ch03.Submission + contract namespace/opens; exact child types, child proofs, parent assembly, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SymmetricVitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeDensityInfiniteSplitDecision.lean`

Pinned snapshot: project d09bc8a and Mathlib 25730c7c, plus the pinned simongmt package.

Reused by the children:
- Vitali.exists_disjoint_covering_ae (Vitali.lean:237)
- Measure.addHaar_closedBall' (EqHaar.lean:475)
- isAddHaarMeasure_euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:104)
- Isometry.euclideanHausdorffMeasure_image (same file, :131)
- isometry_subtype_coe, Subtype.borelSpace, Subtype.dist_eq

Used by the parent assembly:
- Submodule.starProjection_apply_mem (Projection/Basic.lean:156)
- measure_biUnion (Measure/Basic.lean:132) and measure_biUnion_le (OuterMeasure/Basic.lean:74)
- ENNReal.Tendsto.const_div (ENNReal/Lemmas.lean:476) and ENNReal.tendsto_ofReal_atTop (:160)

No usable match for either child's fact:
- The contract has no Vitali or plane-disc lemma.
- Mathlib states Haar and Vitali facts only on whole spaces.
- SimonGMT's Chapter04 planeMeasure_unit_closedBall covers only the unit ball at 0 with n > 0. Chapter01 hasSymmetricVitaliProperty_of_finite_doubling requires finite total mass. Neither module is imported by GMT.Ch03.Submission (which imports only Chapter02.BV and Chapter03.Rectifiable).
- No DAG node reserves a bf_plane_* name.

The two plane facts are therefore supplied by the new children. Simon Ch. 1, 2.9 (lines 445–470), 3.4–3.5 (lines 609–660) and 3.10–3.11(2) (lines 765–799) are their textual sources.

The machine check in GMT/Scratch/ConeDensityInfiniteSplitDecision.lean compiles. Both exact child types and the frozen parent type are proved there, with axioms only [propext, Classical.choice, Quot.sound].
