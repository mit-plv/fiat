#!/bin/bash

set -e

PREV_TIME=$(date +%s.%N)
PREV=""
DO_PRINT=""

while read i
do
    NEXT="$(date +%s.%N)"
    DIFF="$(echo "$NEXT - $PREV_TIME" | bc)"
    if [ ! -z "$DO_PRINT" ];
    then
	echo "$DIFF: $PREV"
    else
	DO_PRINT="yes"
    fi
    PREV="$i"
    PREV_TIME="$NEXT"
done
