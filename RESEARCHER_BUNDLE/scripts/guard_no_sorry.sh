#!/bin/bash
# guard_no_sorry.sh - Quick check for sorry/admit in Lean source files
#
# Usage: ./scripts/guard_no_sorry.sh
#
# Exits with code 1 if any sorry or admit is found.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUNDLE_DIR="$(dirname "$SCRIPT_DIR")"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

if grep -rn "\b\(sorry\|admit\)\b" "$BUNDLE_DIR/HeytingLean/" --include="*.lean" 2>/dev/null; then
    echo -e "${RED}FAILED: Found sorry or admit in source files${NC}"
    exit 1
fi

echo -e "${GREEN}PASSED: No sorry or admit found${NC}"
