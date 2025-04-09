N=7
S=64

DIR="$PWD/cnfs"

CNF="$DIR/g${N}_${S}.cnf"
DSR="$DIR/g${N}_${S}.dsr"
CUBES="$DIR/g${N}_${S}_cubes.icnf"

LSR="$DIR/g${N}_${S}.lsr"
SB="$DIR/g${N}_${S}_sb.cnf"

TAUTO="$DIR/g${N}_${S}_tauto.cnf"

TMPDIR="tmp"

set -e -x

PATH="/home/james/Projects/sat/dsr-trim/src:/home/james/Projects/sat/drat-trim:$PATH"
#PATH="/home/james/Projects/dsr-trim/src:/home/james/Projects/drat-trim:$PATH"

(cd ../..; LEAN_ABORT_ON_PANIC=1 lake exe keller cnf $N $S --cnf $CNF --dsr $DSR --cube $CUBES)

# check the SR proof
time dsr-trim -f $CNF $DSR $LSR --emit-valid-formula-to=$SB
lsr-check $CNF $LSR

# check that the cubes negated leads to tautology
(cd ../..; LEAN_ABORT_ON_PANIC=1 lake exe keller negate-cubes --cnf $SB --cubes $CUBES --out $TAUTO)
cadical $TAUTO || true

# shuffle the cubes and start runnin em
(echo "p inccnf"; grep -v "^p" $SB; cat $CUBES | shuf) |
    cadical

