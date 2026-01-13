#!/bin/bash
# verify_assembly.sh - One-command verification for Assembly Theory formalization
#
# Usage: ./scripts/verify_assembly.sh
#
# This script:
# 1. Checks prerequisites (lake, lean)
# 2. Checks for forbidden markers (sorry, admit)
# 3. Runs strict build with warnings as errors
# 4. Prints axiom dependencies
# 5. Generates checksums

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUNDLE_DIR="$(dirname "$SCRIPT_DIR")"
REPORTS_DIR="$BUNDLE_DIR/reports"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=============================================="
echo " Assembly Theory Formalization Verification"
echo "=============================================="
echo ""

# Check prerequisites
for cmd in grep tee sort find; do
  command -v "$cmd" >/dev/null 2>&1 || { echo -e "${RED}FAILED: missing '$cmd'${NC}"; exit 1; }
done

command -v lake >/dev/null 2>&1 || { echo -e "${RED}FAILED: 'lake' not found. Install Lean via elan.${NC}"; exit 1; }
command -v lean >/dev/null 2>&1 || { echo -e "${RED}FAILED: 'lean' not found. Install Lean via elan.${NC}"; exit 1; }

mkdir -p "$REPORTS_DIR"

# Step 1: Guard check for sorry/admit
echo -e "${YELLOW}[1/4] Checking for forbidden markers...${NC}"
if grep -rn "\b\(sorry\|admit\)\b" "$BUNDLE_DIR/HeytingLean/" --include="*.lean" 2>/dev/null; then
    echo -e "${RED}FAILED: Found sorry or admit in source files${NC}"
    exit 1
fi
echo -e "${GREEN}PASSED: No sorry or admit found${NC}"
echo ""

# Step 2: Strict build (pipefail ensures lake failures are caught)
echo -e "${YELLOW}[2/4] Running strict build...${NC}"
cd "$BUNDLE_DIR"

lake build -- -DwarningAsError=true 2>&1 | tee "$REPORTS_DIR/BUILD_TRANSCRIPT.txt"
echo -e "${GREEN}PASSED: Build completed successfully${NC}"
echo ""

# Step 3: Axiom audit (using committed script, not /tmp)
echo -e "${YELLOW}[3/4] Auditing axioms...${NC}"
lake env lean "$SCRIPT_DIR/print_axioms.lean" 2>&1 | tee "$REPORTS_DIR/AXIOMS_PRINT.txt"
echo -e "${GREEN}Axiom audit complete${NC}"
echo ""

# Step 4: Generate checksums
echo -e "${YELLOW}[4/4] Generating checksums...${NC}"
find "$BUNDLE_DIR/HeytingLean" -name "*.lean" -exec sha256sum {} \; | sort > "$REPORTS_DIR/SHA256SUMS.txt"
echo -e "${GREEN}Checksums generated${NC}"
echo ""

echo "=============================================="
echo -e "${GREEN} VERIFICATION COMPLETE ${NC}"
echo "=============================================="
echo ""
echo "Reports saved to: $REPORTS_DIR/"
echo "  - BUILD_TRANSCRIPT.txt"
echo "  - AXIOMS_PRINT.txt"
echo "  - SHA256SUMS.txt"
echo ""
echo "All checks passed!"
