#!/usr/bin/env bash
find src -name "*.agda" ! -name "Examples.agda" -exec agda {} \;
find src -name "Examples.agdai" -type f -delete
time find src -name "Examples.agda" -exec agda {} \;
