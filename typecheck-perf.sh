#!/usr/bin/env bash
find src -name "*.agdai" -type f -delete
find src -name "*.agda" ! -name "Examples.agda" -exec agda {} \;
time find src -name "Examples.agda" -exec agda {} \;
