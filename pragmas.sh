#!/bin/bash
pragma="{-# OPTIONS --without-K --safe #-}"
pragmanl=$'{-# OPTIONS --without-K --safe #-}\n\n'
find . -type f -name "*.agda" | while read -r file
do
    firstline=$(head -1 "$file")
    if [ "$firstline" != "$pragma" ]; then
        ex -sc "1i|$pragmanl" -cx "$file"
    fi
done
