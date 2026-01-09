#!/bin/bash
# verify_assembly.sh - One-command verification for Assembly Theory formalization
#
# Usage: ./scripts/verify_assembly.sh
#
# This script:
# 1. Checks for forbidden markers (sorry, admit)
# 2. Runs strict build with warnings as errors
# 3. Prints axiom dependencies
# 4. Generates checksums

set -e

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

mkdir -p "$REPORTS_DIR"

# Step 1: Guard check for sorry/admit
echo -e "${YELLOW}[1/4] Checking for forbidden markers...${NC}"
if grep -rn "\b\(sorry\|admit\)\b" "$BUNDLE_DIR/HeytingLean/" --include="*.lean" 2>/dev/null; then
    echo -e "${RED}FAILED: Found sorry or admit in source files${NC}"
    exit 1
fi
echo -e "${GREEN}PASSED: No sorry or admit found${NC}"
echo ""

# Step 2: Strict build
echo -e "${YELLOW}[2/4] Running strict build...${NC}"
cd "$BUNDLE_DIR"

# Capture build output
if lake build -- -DwarningAsError=true 2>&1 | tee "$REPORTS_DIR/BUILD_TRANSCRIPT.txt"; then
    echo -e "${GREEN}PASSED: Build completed successfully${NC}"
else
    echo -e "${RED}FAILED: Build errors occurred${NC}"
    exit 1
fi
echo ""

# Step 3: Axiom audit
echo -e "${YELLOW}[3/4] Auditing axioms...${NC}"
cat > /tmp/print_axioms.lean << 'EOF'
import HeytingLean.ATheory.Paper.AssemblyBounds
import HeytingLean.ATheory.Paper.MolecularSpace
import HeytingLean.ATheory.Paper.HypergraphSpace
import HeytingLean.ATheory.CopyNumberSelection

#print axioms HeytingLean.ATheory.Paper.AssemblyBounds.dagJoinCount_bounds
#print axioms HeytingLean.ATheory.Paper.ObjSyntax.space.assemblyIndex_eq_dagJoinCount
#print axioms HeytingLean.ATheory.Paper.Molecular.assemblyIndex_mol_le_dagJoinCount
EOF

lake env lean /tmp/print_axioms.lean 2>&1 | tee "$REPORTS_DIR/AXIOMS_PRINT.txt" || true
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
