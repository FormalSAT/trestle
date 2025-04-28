N=6
S=32

DIR="$PWD/cnfs"

CNF="$DIR/g${N}_${S}.cnf"
DSR="$DIR/g${N}_${S}.dsr"
CUBES="$DIR/g${N}_${S}_cubes.icnf"

LSR="$DIR/g${N}_${S}.lsr"
SB="$DIR/g${N}_${S}_sb.cnf"

TAUTO="$DIR/g${N}_${S}_tauto.cnf"

set -e -x

(cd ../..; LEAN_ABORT_ON_PANIC=1 lake build keller srcheck)

PATH="$PWD/../../.lake/build/bin:$PATH"

PATH="/home/james/Projects/sat/dsr-trim/src:/home/james/Projects/sat/drat-trim:$PATH"
#PATH="/home/james/Projects/dsr-trim/src:/home/james/Projects/drat-trim:$PATH"

keller cnf $N $S --cnf $CNF --dsr $DSR --cube $CUBES

# check the SR proof
time dsr-trim -f $CNF $DSR $LSR
lsr-check $CNF $LSR
srcheck $CNF $LSR

# make the CNF with SB clauses
keller append-sr-clauses --cnf $CNF --sr $DSR --out $SB

# check that the cubes negated leads to tautology
keller negate-cubes --cnf $SB --cubes $CUBES --out $TAUTO
cadical $TAUTO || true

# shuffle the cubes and start runnin em
(echo "p inccnf"; grep -v "^p" $SB; cat $CUBES | shuf) |
    cadical

