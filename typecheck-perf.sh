#!/usr/bin/env bash
find src -name "*.agdai" -type f -delete
time find src -name "Examples.agda" -exec agda {} \;
