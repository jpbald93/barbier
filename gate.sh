#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED theorem, and each report is present exactly once;
#  * each REQUIRED theorem (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED theorems.
# REQUIRED lists, fully qualified, every declaration of this library cited in SPIKE_REPORT.md
# plus every name queried by scratch/Ax.lean; definitions may use a subset of the standard axioms.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="Barbier"
LIB="Barbier"
REQUIRED="eVariationOn_eq_integral_norm_deriv Barbier.ConstWidthSupport Barbier.barbier Barbier.bridge_constWidth Barbier.bridge_curve Barbier.bridge_inner_exp Barbier.bridge_perimeter Barbier.bridge_support Barbier.bridge_trefoil Barbier.circle_constWidth Barbier.circle_perimeter Barbier.contDiff_one_deriv Barbier.curve Barbier.curve_proj Barbier.curve_width Barbier.deriv_curve Barbier.deriv_deriv_trefoil Barbier.deriv_trefoil Barbier.hasDerivAt_curve Barbier.hasDerivAt_trefoil Barbier.integral_deriv_deriv_eq_zero Barbier.integral_support_eq Barbier.norm_deriv_curve Barbier.norm_deriv_curve_of_convex Barbier.perimeter Barbier.perimeter_eq_integral Barbier.trefoil Barbier.trefoil_constWidth Barbier.trefoil_not_const Barbier.trefoil_perimeter Barbier.eVariationOn_eq_integral_norm_deriv Barbier.PiecewiseConstWidth Barbier.ConstWidthSupport.toPiecewise Barbier.barbier_piecewise Barbier.reuleauxPiece Barbier.reuleaux Barbier.reuleaux_periodic Barbier.reuleaux_width Barbier.reuleaux_constWidth Barbier.reuleaux_perimeter Barbier.reuleaux_not_smooth Barbier.reuleaux_vertices Barbier.reuleaux_arc Barbier.perimeter_eq_eVariationOn Barbier.body Barbier.convex_body Barbier.curve_mem_body Barbier.support_body Barbier.width_body Barbier.bridge_support_piecewise Barbier.curve_mem_body_piecewise Barbier.support_body_piecewise Barbier.width_body_piecewise Barbier.eVariationOn_ne_top_of_contDiff Barbier.length_eq_integral_norm_deriv Barbier.reuleaux_length_ne_top Barbier.reuleaux_perimeter_eq_eVariationOn Barbier.reuleaux_length Barbier.isCompact_body_piecewise Barbier.body_nonempty_piecewise Barbier.exists_convexBody_piecewise Barbier.reuleaux_convexBody Barbier.l14b_curve Barbier.l14b_perimeter Barbier.l14b_body Barbier.l14b_constWidth Barbier.l14b_piecewise Barbier.l14b_piecewise_iff Barbier.l14b_reuleaux Barbier.l14b_contDiff_curve Barbier.l14_barbier Barbier.l14_toPiecewise Barbier.l14_barbier_piecewise Barbier.l14_reuleaux Barbier.l14_length Barbier.l14_perimeter_eq_eVariationOn Barbier.l14_body Barbier.l14_convexBody Barbier.l14_reuleaux_convexBody Barbier.l14w_barbier Barbier.l14w_reuleaux Barbier.l14w_length Barbier.Classical.cov_supportFn_obligation Barbier.Classical.isPlaneConvexBody_iInter Barbier.Classical.cov_C1_a_support Barbier.Classical.cov_C1_b_part Barbier.Classical.cov_C1_a_part Barbier.Classical.cov_C1_b_equiv_part Barbier.Classical.isPlaneConvexBody_reuleaux Barbier.Classical.reuleaux_not_disk Barbier.Classical.cov_C2_a_part Barbier.Classical.cov_C2_b_part Barbier.Classical.cov_C2_c_disk_area Barbier.Classical.cov_C2_reuleaux_polygon_part Barbier.Classical.angle_equilateral Barbier.Classical.cov_C2_boundary_part"
SOURCES="Barbier/*.lean Barbier.lean"
# Never fetch: the pinned Mathlib checkout must already be present.
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
# The `#print axioms` queries are generated here rather than read from a file in the repo.
# Portable (no GNU mktemp); the leading dot keeps it out of the SOURCES glob.
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
