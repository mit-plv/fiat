#!/bin/bash

set -e

LINE=0

while read i
do
    LINE="$(($LINE + 1))"
    echo "Line $LINE: $i"
done
