#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SELF="$(readlink -f "${BASH_SOURCE[0]}")"

#set -x

cd "$DIR/.."

# update makefile if we're newer
if [ "$SELF" -nt "$DIR/../Makefile.librarydepgraphs" ] || [ "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh -nt "$DIR/../Makefile.librarydepgraphs" ]
then
   echo "Making makefile"
   # colors for directories come from the list at http://hackage.haskell.org/package/graphviz-2999.13.0.3/docs/Data-GraphViz-Attributes-Colors-X11.html#t:X11Color
   bash "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh "$DIR"/../Makefile.librarydepgraphs -t Fiat -R Fiat=src -R ADTExamples=examples \
    -c src/ADT/=SkyBlue \
    -c src/ADTNotation/=MistyRose \
    -c src/ADTRefinement/BuildADTRefinements/=Sienna1 \
    -c src/ADTRefinement/Refinements/=LightSalmon \
    -c src/ADTRefinement/=Orange \
    -c src/Computation/Refinements/=Indigo \
    -c src/Computation/=Navy \
    -c src/QueryStructure/QuerySpecs/=Maroon \
    -c src/QueryStructure/Refinements/Bags/=HotPink \
    -c src/QueryStructure/Refinements/FMapImplementation/=LightCoral \
    -c src/QueryStructure/Refinements/BagADT/=DeepPink \
    -c src/QueryStructure/Refinements/ListImplementation/=LightPink \
    -c src/QueryStructure/Refinements/=Orchid \
    -c src/QueryStructure/=Magenta \
    -c src/FiniteSetADTs/=RoyalBlue1 \
    -c src/Common/=Turquoise1 \
    -c src/Parsers/=Purple \
    -c src/=Red \
    -c examples/ADTExamples/=LimeGreen \
    -c examples/CacheADT/=YellowGreen \
    -c examples/=LawnGreen

   rm -f "$DIR/../library.svg" "$DIR/../library.dot"
fi

cd "$DIR/.."
HASKELL="runhaskell"
if [ -d ".cabal-sandbox" ]
then
    for i in .cabal-sandbox/*.conf*
    do
	HASKELL="$HASKELL -package-conf=$i"
    done
fi
make -f Makefile.librarydepgraphs library.deps library.dot library.svg HASKELL="$HASKELL"
