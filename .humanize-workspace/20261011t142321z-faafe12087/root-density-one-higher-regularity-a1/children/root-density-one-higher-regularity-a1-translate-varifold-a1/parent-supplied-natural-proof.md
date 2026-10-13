# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (Inv) of the parent-supplied proof (translation invariance), used in its Step 2 to apply Simon's Theorem 5.2 (whose hypotheses 5.1 are centred at 0) at the point xi. Notation: M := V.carrier, theta := V.mult, mu := V.weight, H^n := muHE[n], tau(x) := x - xi with inverse tau^{-1}(y) = y + xi, U' := tau(U).

Facts used. (I1) tau is an isometric bijection of R^(n+l) onto itself (a homeomorphism and a Borel measurable equivalence), and Hausdorff measure is invariant under isometric bijections: H^n(tau(S)) = H^n(S) for every S (Mathlib IsometryEquiv.hausdorffMeasure_image; muHE[n] is a constant multiple of muH[n]). Consequently the image of H^n restricted to S under tau is H^n restricted to tau(S) (MeasurableEquiv.restrict_map), and, by the change-of-variables formula for measurable equivalences, which needs no measurability of the integrand (Mathlib lintegral_map_equiv, MeasurableEquiv.integral_map), integral over tau(S) of g dH^n = integral over S of g(tau x) dH^n(x) for every g >= 0, and likewise for Bochner integrals. (I2) For a homeomorphism tau and a Borel measure nu, spt(tau_# nu) = tau(spt nu): y is outside spt(tau_# nu) iff some open N containing y has nu(tau^{-1} N) = 0 iff tau^{-1}(y) is outside spt nu.

1. Definition. Put M' := tau(M) and theta'(y) := theta(y + xi); let V' be the varifold in U' with carrier M' and multiplicity theta'. We check the structure fields.

2. Fields. (a) M' is contained in U' because M is contained in U. (b) Null-measurability: M is H^n-null-measurable, so there is a Borel set M0 with H^n(M symmetric-difference M0) = 0; then tau(M0) is Borel and H^n(tau(M) symmetric-difference tau(M0)) = H^n(tau(M symmetric-difference M0)) = 0 by (I1). (c) Countable rectifiability: if M is contained in N0 union the union over j of F_j(R^n), with H^n(N0) = 0 and each F_j : R^n -> R^(n+l) Lipschitz, then tau(M) is contained in tau(N0) union the union over j of (tau o F_j)(R^n), H^n(tau(N0)) = 0 by (I1), and tau o F_j is Lipschitz with the same constant. (d) Positivity: if y is in M' then y + xi is in M, so theta'(y) = theta(y + xi) > 0. (e) Measurability: by (I1) the measure H^n restricted to M' is the image of H^n restricted to M under the measurable equivalence tau, and theta' = theta o tau^{-1}; since theta is a.e.-measurable for H^n restricted to M, theta' is a.e.-measurable for the image measure (compose an a.e.-equal measurable representative with tau^{-1}). (f) Local integrability: if K is a compact subset of U', then tau^{-1}(K) = K + xi is a compact subset of U and, by (I1), integral over M' cap K of |theta'| dH^n = integral over M cap (K + xi) of |theta| dH^n < infinity.

3. Weight. For every Borel S, V'.weight(S) = integral over S cap M' of ofReal(theta') dH^n = integral over tau^{-1}(S) cap M of ofReal(theta) dH^n (by the change of variables in (I1) for the measurable equivalence tau, applied to the function indicator(S) * ofReal(theta'), which need not be measurable) = mu(tau^{-1}(S)) = (mu.map tau)(S). Two Borel measures agreeing on Borel sets are equal, so V'.weight = V.weight.map (fun x => x - xi). Consequently, for every Borel g >= 0 and every mu-integrable g, integral of g d(V'.weight) = integral of g(tau x) dmu(x).

4. Support. V'.support = U' cap spt(V'.weight) = tau(U) cap tau(spt mu) by step 3 and (I2) = tau(U cap spt mu) since tau is injective = tau(V.support).

5. Tangent projections. For every y, every r and every subspace P: blowUpMap y r '' M' = { r^{-1}((x - xi) - y) : x in M } = blowUpMap (y + xi) r '' M; theta'(y + r z) = theta((y + xi) + r z); and theta'(y) = theta(y + xi). Hence, after rewriting the image sets by set extensionality and the multiplicity arguments by add_right_comm (then funext/propext), the proposition HasWeightedApproximateTangentSpaceAt n M' theta' y P equals the proposition HasWeightedApproximateTangentSpaceAt n M theta (y + xi) P (the dimension condition is identical). Therefore the two existence propositions in the definition of tangentProj coincide, the two dependent if-then-else expressions are equal, and V'.tangentProj y = V.tangentProj (y + xi) for every y. For a C^1 field X' put X := X' o tau; by the chain rule (D tau = identity) DX(x) = DX'(tau x), hence V'.divM X'(tau x) = trace(DX'(tau x) o V'.tangentProj(tau x)) = trace(DX(x) o V.tangentProj(x)) = V.divM X(x) for every x.

6. Generalized mean curvature. Assume V has generalized mean curvature H in U and set H' := H(. + xi) = H o tau^{-1}.
(a) Local integrability of H' on U' for V'.weight: let y in U' and x := y + xi in U. There is a set N in the filter nhdsWithin(x, U) on which H is integrable for mu; then tau(N) belongs to nhdsWithin(y, U') because tau is a homeomorphism with tau(U) = U', and by step 3 integral over tau(N) of |H'| d(V'.weight) = integral over N of |H| dmu < infinity.
(b) First variation: let X' : R^(n+l) -> R^(n+l) be C^1 with compact support and tsupport X' contained in U'. Then X := X' o tau is C^1, has compact support, and tsupport X = tau^{-1}(tsupport X') is contained in U. By step 3 and step 5, integral of V'.divM X' d(V'.weight) = integral of V'.divM X'(tau x) dmu(x) = integral of V.divM X dmu = - integral of <X, H> dmu (generalized mean curvature of V) = - integral of <X'(tau x), H'(tau x)> dmu(x) = - integral of <X', H'> d(V'.weight). Together with (a) this says V'.HasGeneralizedMeanCurvature (fun y => H (y + xi)).

All five asserted properties (carrier, multiplicity, weight, support, transfer of generalized mean curvature) are established in steps 1, 3, 4 and 6.

## Key steps

1. define V' with carrier tau(M) and multiplicity theta(. + xi)
2. verify the structure fields using isometry invariance of H^n
3. the weight of V' is tau_# mu_V and its support is tau(spt V)
4. blow-ups coincide, so tangentProj' y = tangentProj(y + xi) and divM transforms covariantly
5. transfer local integrability and the first variation identity by change of variables

## Reference use

### local-project

Queries:
- `rg -l 'dohr_' <snapshot> .lake/packages/simongmt GMT .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes`
- `rg -n '^import' <snapshot>/project/GMT/Ch05/Contract.lean`
- `lean /tmp/dohr-check/src/T1.lean (#check ContinuousLinearMap.adjoint and LinearMap.normDet after import GMT.Ch05.Submission)`
- `rg -n 'theorem ae_tendsto_rnDeriv \(' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'lemma measure_compl_support :' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem hausdorffMeasure_image \(e : X ≃ᵢ Y\)|theorem hausdorffMeasure_homothety_image' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `for pat in Schauder Campanato 'difference quotient' '[Vv]arifold' 'Legendre-Hadamard'; do rg -l "$pat" <snapshot>/mathlib/Mathlib | wc -l; done`
- `grep -rn 'def normDet' .lake/packages/mathlib/Mathlib`
- `grep -n 'HasWeightedApproximateTangentSpaceAt' -r .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'theorem injective_area_formula_lipschitzOn' -A 12 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `grep -rn 'def areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02`
- `rg -n 'def lpMeanCurvatureKappa' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `lake env lean -o /tmp/dohr-check/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-check/build lean /tmp/dohr-check/final/Children.lean'`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-check/build lean /tmp/dohr-check/final/Assembly.lean'`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-check/build lean /tmp/dohr-check/final/Glue.lean'`
- `grep -n '7.1|Schauder' book/chapter-05.txt; sed -n 455,575p book/chapter-04.txt; sed -n 595,724p book/chapter-01.txt`
- `python3 -I /tmp/dohr-scripts/pdftext.py gm.pdf gm.txt, then regex search for 'Theorem 5.19', 'Theorem 5.20', 'Proposition 8.6', 'Theorem 4.9', '(8.5)', '(3.17)' in the Giaquinta-Martinazzi text (https://www2.karlin.mff.cuni.cz/~kaplicky/pages/pages/2020z/gm.pdf)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dohr-check/final/Children.lean`
- `/tmp/dohr-check/final/Assembly.lean`
- `/tmp/dohr-check/final/Glue.lean`
- `/tmp/dohr-check/final/stmts.json`
- `/tmp/dohr-scripts/gm.txt`

Pinned snapshot (manifest.json): project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace copy. No prior proof or 'dohr_' name exists in the snapshot, simongmt, GMT/ or the DAG (rg returns no matches), so all 9 proposed names are free.

The contract's imports reach neither ContinuousLinearMap.adjoint nor LinearMap.normDet (Lean reports 'Unknown constant'). The graph area element is therefore written as sqrt(Matrix.det (1 + Gram matrix)). Lean examples confirm that 1 is the identity matrix and + is entrywise.

Usable Mathlib items: Besicovitch.ae_tendsto_rnDeriv (Besicovitch.lean:1078), VitaliFamily differentiation (Differentiation.lean), Measure.measure_compl_support (Support.lean:202), and IsometryEquiv.hausdorffMeasure_image / hausdorffMeasure_homothety_image (Hausdorff.lean:845, 1060).

Mathlib has no Schauder, Campanato, Legendre-Hadamard or varifold theory: 'Schauder' matches only Schauder-basis files, the other patterns match nothing, and 'difference quotient' matches only UniformLimitsDeriv.lean.

simongmt provides HasWeightedApproximateTangentSpaceAt and its .unique (Chapter03/Rectifiable.lean:330, 345), injective_area_formula_lipschitzOn (Chapter02/AreaDomain.lean:147), areaJacobianAt = normDet of the derivative (Chapter02/Area.lean:26), and lpMeanCurvatureKappa = (p-n)/(4p) (Chapter04/LpMeanCurvature.lean:76). Its Chapter 4 monotonicity is stated only for the stronger Chapter04.RectifiableVarifold, hence the local monotonicity and tangent-plane children.

Lean checks with the pinned toolchain against a compiled scratch GMT.Ch05.Submission:
- all 9 child statements elaborate (Children.lean);
- Assembly.lean proves DensityOneHigherRegularity from them and allard_regularity_theorem with no sorry of its own (axioms: propext, sorryAx, Classical.choice, Quot.sound);
- Glue.lean confirms that the measurability conjunct restricts to sub-balls.

Book: Theorem 7.1 and its proof are at chapter-05.txt l.1312-1366, monotonicity 4.1-4.10 at chapter-04.txt l.455-575, and comparison/density theorems at chapter-01.txt 3.3-3.6.

Giaquinta-Martinazzi (2nd ed., 2012), extracted text, confirms: Theorem 5.19 (Hoelder coefficients and C^{0,sigma} data give Du in C^{0,sigma}_loc), Theorem 5.20 (C^{k+1,sigma}_loc for k >= 1), Proposition 8.6 (difference quotients for D_alpha A(Du) = 0 under (8.5)), Theorem 4.9, and Definition 3.36 / Remark 3.37 (Legendre implies Legendre-Hadamard).
