#!/usr/bin/env bash
agda "src/Examples.agda"
rm "src/Examples.agdai"
time agda "src/Examples.agda"
