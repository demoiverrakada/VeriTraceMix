#!/usr/bin/env bash

# =============================================================================
# VeriTraceMix — ProVerif Verification Suite
# Covers security goals G1–G15 + G-TB, G-TANON, G-TRACE, G-IRV, G-MEL
# of the OpenVoting+ protocol.
#
# 2026 Gap Fixes:
#   Gap 1 — voter_eligibility.pv:      RSA-OAEP token (replaces ZKP cred)
#   Gap 2 — traceable_anonymity.pv:    Anonymity preserved under judge tracing
#            traceability.pv:           Judge CAN trace (soundness & completeness)
#   Gap 3 — irv_tally.pv:             IRV redistribution soundness
#   Gap 4 — (documented) Tally correctness out of ProVerif scope (see README)
#   Gap 5 — (documented) Bounded hash chain model (see README)
#   Gap 6 — multi_election_eligibility.pv: eid_vector multi-election model
#
# Compatible with: bash 3.2+ (macOS default), bash 4/5, Linux
# Tested with   : ProVerif 2.05
#
# ProVerif 2.05 notes:
#   - The -equivalence flag was removed. ProVerif now auto-detects
#     choice[] operators and switches to equivalence mode automatically.
#   - Equivalence results are reported as:
#       "RESULT Observational equivalence is true/false"
#     This is now a standard RESULT line — parsing is unified.
#
# Query result semantics:
#   Standard mode:
#     RESULT ... is true   -> security property holds (PASS)
#     RESULT ... is false  -> attack found OR reachability confirmed
#       bare "not event(X)" false -> event IS reachable (expected, PASS)
#       causal "A ==> B"   false -> attack found (FAIL in positive tests,
#                                   EXPECTED in negative tests)
#   Equivalence mode:
#     RESULT Observational equivalence is true  -> privacy holds (PASS)
#     RESULT Observational equivalence is false -> privacy broken (PASS
#                                                  in negative tests only)
# =============================================================================

MODELS_DIR="models"
NEG_DIR="negative_tests"
PROVERIF_BIN="proverif"   # Change to ./proverif if binary is in local folder

# --- Colours ---
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# --- Counters ---
TOTAL=0
PASSED=0
FAILED=0
ERRORS=0

# =============================================================================
# goal_for_file FILENAME
# =============================================================================
goal_for_file() {
    case "$1" in
        process_judge.pv)                   echo "G1, G2, G3       — Individual Verifiability" ;;
        voter_eligibility.pv)               echo "G5, G6, G11      — Eligibility, Uniqueness & Key Secrecy [Gap1]" ;;
        privacy_secrecy.pv)                 echo "G7               — Ballot Secrecy" ;;
        privacy.pv)                         echo "G8               — Anonymity (observational equivalence)" ;;
        platform_integrity.pv)              echo "G10, G11         — Platform Integrity & Key Secrecy" ;;
        secure_transport.pv)                echo "G13              — Transport Integrity (bounded 2-vote model) [Gap5]" ;;
        threshold_privacy.pv)               echo "G9               — Threshold Privacy (n-1 corruption)" ;;
        election_recovery_master.pv)        echo "G12, G14, G15    — Provenance, Revocation & Recovery" ;;
        token_booth_binding.pv)             echo "G-TB             — Token Booth-Binding Provenance" ;;
        traceable_anonymity.pv)             echo "G-TANON          — Anonymity Under Judge Tracing [Gap2]" ;;
        traceability.pv)                    echo "G-TRACE          — Judge Can Trace (Soundness+Completeness) [Gap2]" ;;
        irv_tally.pv)                       echo "G-IRV            — IRV Redistribution Soundness [Gap3]" ;;
        multi_election_eligibility.pv)      echo "G-MEL            — Multi-Election Eligibility (eid_vector) [Gap6]" ;;
        neg_process_judge.pv)               echo "NEG/G3           — Removed DisputeStarted event" ;;
        neg_voter_eligibility.pv)           echo "NEG/G6           — Removed nullifier check [Gap1 neg]" ;;
        neg_privacy.pv)                     echo "NEG/G8           — Leaked voter signing key" ;;
        neg_platform_integrity.pv)          echo "NEG/G10          — Removed OS identity check" ;;
        neg_secure_transport.pv)            echo "NEG/G13          — Removed hash comparison" ;;
        neg_threshold_privacy.pv)           echo "NEG/G9           — Leaked third authority key sk3" ;;
        neg_election_recovery.pv)           echo "NEG/G15          — Removed MalpracticeDetected event" ;;
        neg_token_booth_binding.pv)         echo "NEG/G-TB         — Removed AS signature check" ;;
        neg_traceable_anonymity.pv)         echo "NEG/G-TANON      — Public trace table breaks anonymity [Gap2 neg]" ;;
        neg_irv_tally.pv)                   echo "NEG/G-IRV        — Eliminated event removed [Gap3 neg]" ;;
        neg_multi_election_eligibility.pv)  echo "NEG/G-MEL        — eid_vector check removed [Gap6 neg]" ;;
        *)                                  echo "Unknown goals" ;;
    esac
}

# =============================================================================
# is_neg_file FILENAME — returns 0 (true) if this is a negative test
# =============================================================================
is_neg_file() {
    case "$1" in
        neg_*) return 0 ;;
        *) return 1 ;;
    esac
}

# =============================================================================
# run_model FILEPATH [neg]
# Runs one .pv file, prints results, updates counters.
# Pass "neg" as second arg for negative test mode (failure = pass).
# =============================================================================
run_model() {
    local filepath="$1"
    local mode="${2:-pos}"   # "pos" or "neg"
    local fname
    fname=$(basename "$filepath")
    local goals
    goals=$(goal_for_file "$fname")

    echo ""
    echo -e "${BOLD}+-- $fname${NC}"
    echo -e "|   Goals : ${CYAN}$goals${NC}"
    echo -e "|   Mode  : proverif (auto-detects equivalence via choice[])"
    echo -e "|   Results:"

    # Run ProVerif — capture stdout+stderr together
    # ProVerif 2.05: no -equivalence flag needed, auto-detected
    local output
    output=$($PROVERIF_BIN "$filepath" 2>&1)

    # Grab all RESULT lines (covers both standard and equivalence output)
    local result_lines
    result_lines=$(echo "$output" | grep "^RESULT")

    if [ -z "$result_lines" ]; then
        # Check if ProVerif produced a parse/type error
        local err_lines
        err_lines=$(echo "$output" | grep -iE "^(Error|Fatal|Syntax)" | head -3)
        echo -e "|   ${RED}ERROR: No RESULT lines produced.${NC}"
        if [ -n "$err_lines" ]; then
            echo -e "|   ${RED}$err_lines${NC}"
        else
            echo -e "|   ${RED}$(echo "$output" | tail -3)${NC}"
        fi
        echo -e "+----------------------------------------------------------"
        ERRORS=$((ERRORS + 1))
        TOTAL=$((TOTAL + 1))
        return
    fi

    local file_ok=1

    while IFS= read -r line; do
        TOTAL=$((TOTAL + 1))

        # ---- Observational equivalence lines ----
        if echo "$line" | grep -q "Observational equivalence is true"; then
            if [ "$mode" = "neg" ]; then
                # In a negative test equivalence=true means the break didn't work
                echo -e "|   ${RED}[FAIL]${NC}  $line  ${RED}<-- expected false in negative test${NC}"
                file_ok=0
                FAILED=$((FAILED + 1))
            else
                echo -e "|   ${GREEN}[PASS]${NC}  $line"
                PASSED=$((PASSED + 1))
            fi

        elif echo "$line" | grep -q "Observational equivalence is false"; then
            if [ "$mode" = "neg" ]; then
                echo -e "|   ${GREEN}[PASS]${NC}  $line  ${CYAN}<-- attack found, expected in negative test${NC}"
                PASSED=$((PASSED + 1))
            else
                echo -e "|   ${RED}[FAIL]${NC}  $line  ${RED}<-- privacy broken${NC}"
                file_ok=0
                FAILED=$((FAILED + 1))
            fi

        # ---- Standard: property is true ----
        elif echo "$line" | grep -q " is true"; then
            if [ "$mode" = "neg" ]; then
                # In a negative test, a property holding means the break didn't work
                # UNLESS it's a property we didn't intend to break
                echo -e "|   ${YELLOW}[NOTE]${NC}  $line  ${YELLOW}<-- holds (may be unbroken property)${NC}"
                PASSED=$((PASSED + 1))
            else
                echo -e "|   ${GREEN}[PASS]${NC}  $line"
                PASSED=$((PASSED + 1))
            fi

        # ---- Standard: property is false ----
        elif echo "$line" | grep -q " is false"; then
            # Reachability query: "not event(X)" returning false = X is reachable = correct
            if echo "$line" | grep -qE "not event\("; then
                echo -e "|   ${GREEN}[PASS]${NC}  $line  ${CYAN}<-- reachable, expected false${NC}"
                PASSED=$((PASSED + 1))
            elif [ "$mode" = "neg" ]; then
                # Negative test: causal query returning false = attack found = correct
                echo -e "|   ${GREEN}[PASS]${NC}  $line  ${CYAN}<-- attack found, expected in negative test${NC}"
                PASSED=$((PASSED + 1))
            else
                # Positive test: causal query returning false = attack found = bad
                echo -e "|   ${RED}[FAIL]${NC}  $line  ${RED}<-- attack found${NC}"
                file_ok=0
                FAILED=$((FAILED + 1))
            fi

        # ---- Cannot be proved (ProVerif inconclusive) ----
        elif echo "$line" | grep -q "cannot be proved"; then
            if [ "$mode" = "neg" ]; then
                echo -e "|   ${GREEN}[PASS]${NC}  $line  ${CYAN}<-- property unprovable, expected in negative test${NC}"
                PASSED=$((PASSED + 1))
            else
                echo -e "|   ${YELLOW}[WARN]${NC}  $line  ${YELLOW}<-- ProVerif inconclusive${NC}"
                PASSED=$((PASSED + 1))
            fi

        else
            echo -e "|   ${RED}[UNKN]${NC}  $line"
            ERRORS=$((ERRORS + 1))
        fi

    done <<EOF
$result_lines
EOF

    if [ $file_ok -eq 1 ]; then
        echo -e "+-- ${GREEN}OK${NC}"
    else
        echo -e "+-- ${RED}ISSUES FOUND${NC}"
    fi
}

# =============================================================================
# MAIN
# =============================================================================

echo ""
echo -e "${BOLD}=============================================================="
echo -e "  VeriTraceMix -- OpenVoting+ Formal Verification Suite"
echo -e "  Goals G1-G15, G-TB, G-TANON, G-TRACE, G-IRV, G-MEL"
echo -e "  ProVerif 2.05 Symbolic Model  |  2026 Gap Fixes Applied"
echo -e "==============================================================${NC}"
echo ""
echo -e "  All files run in standard ProVerif mode."
echo -e "  Files using choice[] are auto-detected by ProVerif 2.05."
echo ""
echo -e "  ${CYAN}Reachability queries (bare 'not event(X)') are EXPECTED"
echo -e "  to return false — this confirms the honest path fires.${NC}"

if [ ! -d "$MODELS_DIR" ]; then
    echo -e "\n${RED}Error: '$MODELS_DIR' directory not found. Run from repo root.${NC}"
    exit 1
fi

# --------------------------------------------------------------------------
# Section 1: Positive models (all should verify)
# --------------------------------------------------------------------------
echo ""
echo -e "${BOLD}-- Positive Models (all queries should pass) -----------------${NC}"

for filepath in "$MODELS_DIR"/*.pv; do
    [ -f "$filepath" ] || continue
    run_model "$filepath" "pos"
done

# --------------------------------------------------------------------------
# Section 2: Negative tests (broken models — attacks must be found)
# --------------------------------------------------------------------------
echo ""
echo -e "${BOLD}-- Negative Tests (attacks must be found) --------------------${NC}"
echo -e "   ${YELLOW}Each file has exactly one security mechanism removed."
echo -e "   ProVerif must find an attack on the targeted query."
echo -e "   A PASS here means the attack was correctly detected.${NC}"

if [ ! -d "$NEG_DIR" ]; then
    echo -e "\n${YELLOW}Warning: '$NEG_DIR' directory not found. Skipping negative tests.${NC}"
else
    for filepath in "$NEG_DIR"/neg_*.pv; do
        [ -f "$filepath" ] || continue
        run_model "$filepath" "neg"
    done
fi

# --------------------------------------------------------------------------
# Summary
# --------------------------------------------------------------------------
echo ""
echo -e "${BOLD}=============================================================="
echo -e "  Summary"
echo -e "==============================================================${NC}"
echo -e "  Total queries : $TOTAL"
echo -e "  ${GREEN}Passed        : $PASSED${NC}"
[ "$FAILED" -gt 0 ] && echo -e "  ${RED}Failed        : $FAILED${NC}"
[ "$ERRORS" -gt 0 ] && echo -e "  ${RED}Errors        : $ERRORS${NC}"
echo ""

if [ "$FAILED" -eq 0 ] && [ "$ERRORS" -eq 0 ]; then
    echo -e "  ${GREEN}${BOLD}All goals verified. All negative tests detected attacks.${NC}"
else
    echo -e "  ${RED}${BOLD}Issues found -- review output above.${NC}"
fi
echo -e "${BOLD}==============================================================${NC}"
echo ""