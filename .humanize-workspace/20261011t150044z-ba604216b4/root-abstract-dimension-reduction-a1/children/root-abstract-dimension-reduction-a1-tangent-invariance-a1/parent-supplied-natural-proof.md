# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.tangent_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, proof of A.4, chapter-A.txt lines 125–134: ψ_{y,1} = ψ for y ∈ S and ψ_{βx,1} = ψ for β ∈ ℝ, hence invariance under the span of S and x. This is Lemma I (step 6) of the parent proof, with its departure [D2]. The parent's hypotheses x ∈ B_1(0) and λ_k decreasing are replaced by the only consequence used, φ_{x,λ_k} ∈ F. Write μ := μH[n] and g_k(z) := φ(x + λ_k z), so g_k ∈ F and g_k ⇀ ψ.
1. Uniqueness of weak limits in F. Let g ∈ F with ∫ f g dμ = ∫ f ψ dμ for every continuous compactly supported f; then g = ψ. Indeed, g and ψ are locally μ-integrable by (H1), and the identity holds in particular for all smooth compactly supported f. So g = ψ μ-a.e. by the fundamental lemma of the calculus of variations, which holds for any Borel measure on a finite-dimensional real space and locally integrable functions (Mathlib ae_eq_of_integral_contDiff_smul_eq). Parent fact (a) gives the classical argument: on a ball B, |g − ψ|μ⌞B is a finite Borel measure; in it, the bounded sign field of each coordinate of g − ψ is an L¹-limit of continuous fields with compact support in B, which forces ∫_B |g − ψ| dμ = 0. Then g = ψ by (H0).
2. Translates of ψ lie in F. Let w ∈ ℝ^P and θ := 1/(2 + |w|). Then 0 < θ ≤ 1/2 < 1 and |θw| = θ|w| ≤ 1 − θ, since θ(1 + |w|) ≤ 1. So z ↦ ψ(θw + θz) belongs to F by (A.1). By homogeneity ψ(θw + θz) = ψ(θ(w + z)) = ψ(w + z). Hence ψ_{w,1} : z ↦ ψ(w + z) belongs to F.
3. Key step. Let w ∈ ℝ^P and c_k > 0 with c_k → 1, and suppose that for all sufficiently large k, g_k(w + z) = g_k(c_k z) for every z. Then ψ(w + z) = ψ(z) for all z. Proof: the g_k are locally integrable by (H1). Let f be continuous with compact support. The sibling lemma adr_weak_tendsto_comp_affine, with translation w and factors 1, gives ∫ f(z) g_k(w + z) dμ → ∫ f(z) ψ(w + z) dμ. With translation 0 and factors c_k, it gives ∫ f(z) g_k(c_k z) dμ → ∫ f(z) ψ(z) dμ. The two sequences of integrals agree for large k, so their limits agree: ∫ f ψ_{w,1} dμ = ∫ f ψ dμ for all such f. By steps 1 and 2, ψ_{w,1} = ψ.
4. Translations in S. Let s ∈ S. For every k and z, λ_k s ∈ S, and S-invariance of φ with λ = 1 gives g_k(s + z) = φ(λ_k s + 1·(x + λ_k z)) = φ(x + λ_k z) = g_k(1·z). Step 3 with w = s and c_k = 1 gives ψ(s + z) = ψ(z) for all z.
5. Translations along x. Let β ∈ ℝ. Since λ_k → 0, there is k₁ with a_k := 1 + βλ_k > 0 for k ≥ k₁. Put c_k := 1/a_k for k ≥ k₁ and c_k := 1 for k < k₁; then c_k > 0 and c_k → 1. For k ≥ k₁ and all z, S-invariance of φ with y = 0 ∈ S and dilation factor a_k > 0 gives g_k(βx + z) = φ(a_k x + λ_k z) = φ(a_k(x + λ_k c_k z)) = φ(x + λ_k c_k z) = g_k(c_k z). Step 3 with w = βx gives ψ(βx + z) = ψ(z) for all z.
6. Conclusion. Let y ∈ S + ℝx, say y = s + βx with s ∈ S and β ∈ ℝ, and let λ > 0 and z ∈ ℝ^P. By steps 4 and 5 and the homogeneity of ψ, ψ(y + λz) = ψ(s + (βx + λz)) = ψ(βx + λz) = ψ(λz) = ψ(z). ∎

## Key steps

1. weak limits in F are unique: fundamental lemma plus (H0)
2. translates ψ(w+·) of the homogeneous ψ belong to F by A.1 with θ = 1/(2+|w|)
3. if a translate of the blow-up sequence eventually equals a dilation of it with factors c_k → 1, then ψ is invariant under that translation (sibling adr_weak_tendsto_comp_affine twice)
4. S-translations commute with blow-ups, and translation by βx equals dilation by 1/(1+βλ_k) via homogeneity of φ; combine with homogeneity of ψ

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'theorem ae_eq_zero_of_integral|theorem ae_eq_of_integral' mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `grep -n '^theorem|^lemma|^instance|^def' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (hausdorffMeasure_smul₀, map_homothety_hausdorffMeasure, hausdorffMeasure_segment, IsAddLeftInvariant instance)`
- `grep -n '^theorem|^lemma' mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean (Real.hausdorffMeasure_of_finrank_lt, Convex.dimH_eq_finrank_vectorSpan, hausdorffMeasure_of_lt_dimH)`
- `grep -n 'theorem banach_steinhaus' mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `grep -rn 'finrank_sup_span_singleton|disjoint_span_singleton|finrank_span_singleton' mathlib/Mathlib/LinearAlgebra/`
- `grep -rn 'def ediam' mathlib/Mathlib/Topology/EMetricSpace/ mathlib/Mathlib/Topology/MetricSpace/`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter01/{HausdorffContentDensity,HausdorffOpenCovers,HausdorffDensityBounds,Hausdorff}.lean`
- `grep -n 'def dimensionalUpperDensity|def dimensionalDensityQuotient' simongmt/Poincare/SimonGMT/Chapter01/*.lean`
- `cat simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `grep -n '3.26|3.27' book/chapter-01.txt; cat -n book/chapter-A.txt`
- `lake env lean /tmp/adr-decomp/Check.lean (ten child types + assembly of Submission.abstract_dimension_reduction + #print axioms)`
- `lake env lean /tmp/adr-decomp/Check2.lean (adr_dimension_bound, adr_extremal_sing_eq proved from stubs of siblings)`
- `lake env lean /tmp/adr-decomp/Check3.lean (adr_tangent_invariance proved from stub of adr_weak_tendsto_comp_affine)`
- `lake env lean /tmp/adr-decomp/Check4.lean (pp.parens #check of child types)`
- `lake env lean /tmp/adr-decomp/Lib.lean (#print axioms simon_theorem_3_26_ii_of_totallyBounded, hausdorff_eq_zero_of_uniform_content_ball_bound, exists_isOpen_superset_ediam_rpow_lt, simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure, AppendixA.rescale_rescale)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffContentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffOpenCovers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/tmp/adr-decomp/Check.lean`
- `/tmp/adr-decomp/Check2.lean`
- `/tmp/adr-decomp/Check3.lean`
- `/tmp/adr-decomp/Check4.lean`
- `/tmp/adr-decomp/Lib.lean`

The snapshot Contract.lean (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The cited snapshot Mathlib files are byte-identical to the build packages.

Mathlib supplies:
- fact (a): ae_eq_of_integral_contDiff_smul_eq, for any Borel measure and locally integrable functions;
- Hausdorff scaling and translation: hausdorffMeasure_smul₀, map_homothety_hausdorffMeasure, and an IsAddLeftInvariant instance;
- hausdorffMeasure_segment;
- dimension facts: Real.hausdorffMeasure_of_finrank_lt, Convex.dimH_eq_finrank_vectorSpan, hausdorffMeasure_of_lt_dimH;
- banach_steinhaus;
- Submodule.finrank_sup_span_singleton;
- Metric.ediam.

The simongmt library proves Simon Ch.1 3.26(2) as simon_theorem_3_26_ii_of_totallyBounded, together with the open-cover enlargement exists_isOpen_superset_ediam_rpow_lt and the normalization bridge to μH. All of these use only propext, Classical.choice and Quot.sound, so they may back adr_content_density and adr_tangent_keeps_measure. simongmt AppendixA/Foundations.lean has only rescaling and data definitions and leaves A.4 open, so A.4 itself is not in the library.

All ten child types elaborate in the contract context. The parent assembly from the ten stubs compiles, and its only non-standard axiom is sorryAx from the stubs. adr_dimension_bound and adr_extremal_sing_eq compile from sibling stubs, and adr_tangent_invariance compiles from the adr_weak_tendsto_comp_affine stub plus Mathlib. The only reserved DAG names are the ten depth-1 names, so the adr_* names do not collide.
