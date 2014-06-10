#!/bin/bash

set -e

while read i
do
    echo "$(date +%s.%N): $i"
done
