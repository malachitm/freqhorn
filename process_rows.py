import csv

feature_name = "Feature 1: Support any positive algebraic expression"
rows_data = [
    ("1a", "Identify algebraic bases during closed-form scan and skip rational cases", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("1b", "Register unique real algebraic bases in RootRegistry with stable symbols", 0.5, 1.5, 3, 0.25, 0.75, 1.5, "Low", "completed"),
    ("1c", "Re-run substitution so repeated algebraic bases reuse the same symbol", 0.5, 1.5, 3, 0.25, 0.75, 1.5, "Low", "completed"),
    ("2a", "Normalize minimal-polynomial coefficients into integer JSON form", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("2b", "Serialize isolating-interval bounds for each registered real root", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("2c", "Emit ordered aux_roots entries in the POLAR payload", 0.5, 1.5, 3.5, 0.25, 0.75, 2, "Low", "completed"),
    ("3a", "Define AlgRootEntry storage for polynomial and interval metadata", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("3b", "Parse poly_coeffs and interval rationals from JSON into GMP values", 0.5, 1.5, 3, 0.25, 0.75, 1.5, "Low", "completed"),
    ("3c", "Validate aux-root parse failures and registry ordering assumptions", 0.5, 0.75, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("4a", "Build generic polynomial evaluation from coefficient vectors", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("4b", "Add unsupported-degree guard and failure path for large polynomials", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("5a", "Allocate CHC variables for registered algebraic roots in stable order", 1, 2, 5, 0.5, 1, 3, "Medium", "completed"),
    ("5b", "Inject algebraic-root equalities into fact, inductive, and query encodings", 1, 2, 5, 0.5, 1, 3, "Medium", "completed"),
    ("5c", "Preserve original CHC variable positional ordering while inserting roots", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "completed"),
    ("6a", "Update generateRootBounds to consume real algebraic registry entries", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("6b", "Extend str_to_expr and evaluateBaseString to resolve _alg_k names", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("6c", "Remove dead sqrt-only helper paths and fallback assumptions", 1, 2, 5, 0.5, 1, 3, "Medium", "not-started"),
    ("7a", "Parse aux_roots before symbolic closed-form generation begins", 0.25, 0.5, 1.5, 0.125, 0.25, 1, "Low", "completed"),
    ("7b", "Add a call-order smoke check for the real algebraic pipeline", 0.25, 0.5, 1.5, 0.125, 0.25, 1, "Low", "completed"),
    ("8a", "Keep a focused real-algebraic regression using pi1.smt2 and unit tests", 0.5, 1, 3, 0.25, 0.5, 1.5, "Medium", "completed"),
    ("8b", "Expand to a representative bench_horn sweep for real algebraic cases", 1, 2, 5, 0.5, 1, 3, "High", "not-started"),
    ("8c", "Fix benchmark-specific parsing and encoding bugs found in the sweep", 1, 2, 6, 0.5, 1, 3.5, "High", "not-started"),
    ("8d", "Document and script the stable real-algebraic regression set", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Medium", "not-started"),
    ("9a", "Encode algebraic constants as coefficient vectors modulo the minimal polynomial", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "completed"),
    ("9b", "Implement multiplication and reduction in the algebraic basis", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "completed"),
    ("9c", "Reconstruct simplified expressions and hook simplifyAlgExpr into the path", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "completed"),
    ("10a", "Detect conjugate ComplexRootOf pairs during the closed-form scan", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("10b", "Compute magnitude polynomials and isolating intervals for complex pairs", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "completed"),
    ("10c", "Persist complex-pair registry metadata for later trig rewriting", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "completed"),
    ("11a", "Rewrite conjugate-pair terms into magnitude/cosine/sine carrier symbols", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "completed"),
    ("11b", "Rewrite negative real bases as period-2 phase entries", 0.5, 1, 3, 0.25, 0.5, 1.5, "Medium", "completed"),
    ("11c", "Stabilize repeated substitution in the two-pass closed-form rewrite", 0.5, 1, 3, 0.25, 0.5, 1.5, "Medium", "completed"),
    ("11d", "Finalize the complex_pairs payload contract for the downstream consumer", 0.5, 1.5, 4, 0.25, 0.75, 2, "High", "not-started"),
    ("12a", "Define ComplexPairEntry storage for magnitude and phase metadata", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Low", "not-started"),
    ("12b", "Parse magnitude polynomial and interval data from complex_pairs JSON", 0.5, 1.5, 3.5, 0.25, 0.75, 2, "Medium", "not-started"),
    ("12c", "Parse cosine/sine metadata and validate the three-carrier layout", 0.5, 1, 3, 0.25, 0.5, 1.5, "Medium", "not-started"),
    ("13a", "Allocate magnitude/cosine/sine CHC carrier variables in stable order", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "not-started"),
    ("13b", "Inject fact-side complex-pair equalities and magnitude constraints", 1, 2, 5, 0.5, 1, 3, "High", "not-started"),
    ("13c", "Inject inductive and query transitions for trig recurrence updates", 1, 2.5, 6, 0.5, 1.25, 3.5, "High", "not-started"),
    ("13d", "Add periodicity lemmas and soundness guards for phase terms", 0.5, 1.5, 4, 0.25, 0.75, 2, "High", "not-started"),
    ("14a", "Generate numeric bounds for magnitude carriers from complex-pair metadata", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Medium", "not-started"),
    ("14b", "Extend SMT declarations and string parsing for magnitude/cosine/sine symbols", 0.5, 1.5, 4, 0.25, 0.75, 2, "Medium", "not-started"),
    ("14c", "Extend numeric base evaluation lookup for complex-pair carrier names", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Medium", "not-started"),
    ("15a", "Parse complex_pairs before symbolic closed-form generation begins", 0.25, 0.5, 1.5, 0.125, 0.25, 1, "Low", "not-started"),
    ("15b", "Add a call-order smoke check for mixed aux_roots and complex_pairs input", 0.25, 0.5, 1.5, 0.125, 0.25, 1, "Low", "not-started"),
    ("16a", "Add focused unit tests for complex-pair helper routines", 0.5, 1, 3, 0.25, 0.5, 1.5, "Medium", "not-started"),
    ("16b", "Add end-to-end regression on pi1.smt2 and representative complex benchmarks", 0.5, 1.5, 4, 0.25, 0.75, 2, "High", "not-started"),
    ("16c", "Fix consumer bugs surfaced by complex benchmark runs", 1, 2, 6, 0.5, 1, 3.5, "High", "not-started"),
    ("16d", "Expand the regression set and document expected complex-root behavior", 0.5, 1, 2.5, 0.25, 0.5, 1.5, "Medium", "not-started"),
]

def pert(o, ml, p):
    return (o + 4 * ml + p) / 6

output_rows = []
violations = []

for sid, name, ho, hml, hp, ao, aml, ap, risk, status in rows_data:
    hpert = round(pert(ho, hml, hp), 2)
    apert = round(pert(ao, aml, ap), 2)
    
    output_rows.append([
        feature_name, sid, name, ho, hml, hp, hpert, ao, aml, ap, apert, risk, status
    ])
    
    if hp <= 3 * ho:
        violations.append(f"Row {sid} (Human): P={hp} <= 3*O={3*ho}")
    if ap <= 3 * ao:
        violations.append(f"Row {sid} (AI): P={ap} <= 3*O={3*ao}")

# Print CSV
header = ["Feature", "Sub-task #", "Sub-task Name", "Human O (h)", "Human ML (h)", "Human P (h)", "Human PERT (h)", "AI O (h)", "AI ML (h)", "AI P (h)", "AI PERT (h)", "Risk", "Status"]
writer = csv.writer(__import__('sys').stdout)
writer.writerow(header)
writer.writerows(output_rows)

print("\n--- VIOLATIONS (P > 3*O check) ---")
if not violations:
    print("None. Every row satisfies P > 3*O.")
else:
    for v in violations:
        print(v)
