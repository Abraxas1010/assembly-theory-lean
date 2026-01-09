# Assembly Theory: Reproducibility Guide

This document explains how to verify and reproduce the Assembly Theory formalization.

## Quick Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_assembly.sh
```

## Prerequisites

- Lean 4 (see `lean-toolchain` for exact version)
- Lake build tool (bundled with Lean)
- Bash shell
- Git (for fetching dependencies)

## Manual Build Steps

### 1. Update Dependencies

```bash
cd RESEARCHER_BUNDLE
lake update
```

### 2. Strict Build

```bash
lake build -- -DwarningAsError=true
```

### 3. Check for Proof Gaps

```bash
rg "\b(sorry|admit)\b" --type lean HeytingLean/
# Expected: no matches
```

### 4. Axiom Audit

```bash
lake env lean --run scripts/print_axioms.lean
```

Expected axioms (standard Lean kernel only):
- `propext`
- `Classical.choice`
- `Quot.sound`

## Verification Script Details

The `verify_assembly.sh` script performs:

1. **Guard Check**: Scans for `sorry` and `admit`
2. **Strict Build**: Compiles with warnings as errors
3. **Axiom Print**: Lists used axioms
4. **Checksums**: Generates SHA256 hashes

## Expected Outputs

After successful verification:

```
reports/
├── BUILD_TRANSCRIPT.txt    # Full build log
├── AXIOMS_PRINT.txt        # Axiom dependencies
└── SHA256SUMS.txt          # File checksums
```

## Troubleshooting

### Build Fails on Dependencies

```bash
rm -rf .lake lake-manifest.json
lake update
lake build
```

### Out of Memory

```bash
lake build -j1  # Single-threaded build
```

### Wrong Lean Version

Check `lean-toolchain` matches your installation:
```bash
cat lean-toolchain
lean --version
```

## Continuous Integration

For CI systems, use:

```bash
#!/bin/bash
set -e
lake update
./scripts/guard_no_sorry.sh
lake build -- -DwarningAsError=true
```

## Checksum Verification

To verify file integrity:

```bash
sha256sum -c reports/SHA256SUMS.txt
```

## Version Pinning

All dependency versions are locked in `lake-manifest.json`. To update:

```bash
lake update
git add lake-manifest.json
git commit -m "Update dependency pins"
```
