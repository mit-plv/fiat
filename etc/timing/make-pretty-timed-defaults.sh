#!/bin/sh

# This is a helper script for make-pretty-timed.sh and
# make-pretty-timed-diff.sh.

# This file sets the default file names of the make-pretty-timed*.sh
# scripts, as well as setting up the MAKE variable.

export NEW_TIME_FILE=time-of-build-after.log
export OLD_TIME_FILE=time-of-build-before.log
export BOTH_TIME_FILE=time-of-build-both.log
export NEW_PRETTY_TIME_FILE=time-of-build-after-pretty.log
export SINGLE_TIME_FILE=time-of-build.log
export SINGLE_PRETTY_TIME_FILE=time-of-build-pretty.log
export TIME_SHELF_NAME=time-of-build-shelf

# this is fragile, I think; try to find a way to make this more
# robust.
export MAKE="make $@"

function relpath() {
    SRC="$(readlink -f "$(pwd)")/"
    TGT="$(readlink -f "$1")"
    RET=""
    while [ ! -z "$SRC$TGT" ]; do
	# strip the first component off both paths
	NEXT_SRC="${SRC#*/}"
	NEXT_TGT="${TGT#*/}"
	CUR_SRC="${SRC%$NEXT_SRC}"
	CUR_TGT="${TGT%$NEXT_TGT}"
	# if they match, then keep going
	if [ "$CUR_SRC" == "$CUR_TGT" ]; then
	    SRC="$NEXT_SRC"
	    TGT="$NEXT_TGT"
	else
	    # if they don't match, then the entirety of the target goes into the return (only relevant the first time)
	    RET="$TGT"
	    TGT=""
	    # and then if we've actually stripped something off of SRC, we add a ../ to the beginning of ret
	    if [ ! -z "$CUR_SRC" ]; then
		RET="../$RET"
		SRC="$NEXT_SRC"
	    fi
	fi
    done
    echo "$RET"
}
