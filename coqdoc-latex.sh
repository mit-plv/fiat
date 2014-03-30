#!/bin/bash

ARGS=(-latex)
for i in "$@"
do
    if [ "x$i" != "x-pdf" -a "x$i" != "x--pdf" ]
    then
	ARGS[${#ARGS[@]}]="$i"
    fi
done

$COQDOC "${ARGS[@]}"
