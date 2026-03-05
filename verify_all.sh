#!/bin/bash

# --- CONFIGURATION ---
MODELS_DIR="models"
VULN_DIR="vulnerabilities"
PROVERIF_BIN="proverif" # Change to ./proverif if binary is in local folder

# Colors for terminal output
GREEN='\033[0;32m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "=============================================================="
echo "      OPEN-VOTING FORMAL VERIFICATION SUITE (G1 - G15)        "
echo "=============================================================="

# 1. RUN SECURE MODELS
echo -e "\n${BLUE} Verifying Secure Protocol Models (Expect: TRUE)${NC}"
echo "--------------------------------------------------------------"

if [ ! -d "$MODELS_DIR" ]; then
    echo -e "${RED}Error: $MODELS_DIR directory not found.${NC}"
else
    for file in "$MODELS_DIR"/*.pv; do
        echo -e "Testing: ${BLUE}$(basename "$file")${NC}"
        # Run proverif and capture results
        $PROVERIF_BIN "$file" | grep "RESULT" | sed 's/RESULT/  -/'
        echo "--------------------------------------------------------------"
    done
fi


echo -e "\n${GREEN}Verification Suite Finished.${NC}"