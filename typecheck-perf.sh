#!/usr/bin/env bash
agda "src/Polynomial/Simple/AlmostCommutativeRing.agda"
agda "src/Polynomial/Simple/Reflection.agda"
[ -f "src/Examples.agdai" ] && rm "src/Examples.agdai"
time agda --no-syntactic-equality "src/Examples.agda"
