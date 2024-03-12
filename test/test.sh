set -v

CNF=test.cnf
CUBES=test.cubes
COMP=test.comp

TMPCNF=test_tmp.cnf
TMPICNF=test_tmp.icnf
TMPDRAT=test_tmp.drat
TMPLRAT=test_tmp.lrat
ITER=1

VARS=$( head -n 1 $CNF | awk '{ print $3 }' )
CLAUSES=$( head -n 1 $CNF | awk '{ print $4 }' )

ASSUMES=$( tail $CUBES -n +$(( $ITER + 1 )) | head -n 1 | sed 's/a //' | sed 's/ 0/ /')
echo "'$ASSUMES'"

ASSUME_COUNT=$( echo $ASSUMES | wc -w )
echo $ASSUME_COUNT

echo "p cnf $VARS $(($CLAUSES + $ASSUME_COUNT))" > $TMPCNF
tail $CNF --lines=+2 >> $TMPCNF
echo "$ASSUMES" | sed -r 's/([0-9]+) /\1 0\n/g' >> $TMPCNF

#echo "p inccnf" > $TMPICNF
#tail $CNF --lines=+2 >> $TMPICNF
#(tail $CUBES --lines=+$(( $ITER+1 )) | head --lines=1) >> $TMPICNF

cadical $TMPCNF $TMPDRAT --quiet --no-binary

#echo "p cnf $VARS $(($CLAUSES + 1))" > $TMPCNF
#tail $CNF --lines=+2 >> $TMPCNF
#(tail $COMP --lines=+$(( $ITER+1 )) | head --lines=1) >> $TMPCNF

drat-trim $TMPCNF $TMPDRAT -L $TMPLRAT

cake_lpr $CNF $COMP $ITER-$(( $ITER+1 )) $TMPLRAT
