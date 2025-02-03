set -o xtrace

CNF=test.cnf
CUBES=test.cubes
COMP=test.comp

TMPCNF=tmp.cnf
TMPICNF=tmp.icnf
TMPDRAT=tmp.drat
TMPLRAT=tmp.lrat
ITER=0

VARS=$( head -n 1 $CNF | awk '{ print $3 }' )
CLAUSES=$( head -n 1 $CNF | awk '{ print $4 }' )

ASSUMES=$( tail $CUBES -n +$(( $ITER + 1 )) | head -n 1 | sed 's/a //' | sed 's/ 0/ /')
echo "'$ASSUMES'"

ASSUME_COUNT=$( echo $ASSUMES | wc -w )
echo $ASSUME_COUNT

echo "p cnf $VARS $(($CLAUSES + $ASSUME_COUNT))" > $TMPCNF
tail $CNF --lines=+2 >> $TMPCNF
echo -n "$ASSUMES" | sed -r 's/([0-9]+) /\1 0\n/g' >> $TMPCNF

cadical $TMPCNF $TMPDRAT --quiet --no-binary

drat-trim $TMPCNF $TMPDRAT -L $TMPLRAT

cake_lpr $TMPCNF $TMPLRAT

cake_lpr $CNF $COMP $ITER-$(( $ITER+1 )) $TMPLRAT
