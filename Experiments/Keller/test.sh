N=6
S=32

DIR="cnfs"
CNF="$DIR/g${N}_${S}.cnf"
DSR="$DIR/g${N}_${S}.dsr"
LSR="$DIR/g${N}_${S}.lsr"
SB="$DIR/g${N}_${S}_sb.cnf"
DRAT="$DIR/g${N}_${S}_sb.drat"
CUBE="$DIR/g${N}_${S}_cubes.icnf"


set -e -x

PATH="/home/james/Projects/sat/dsr-trim/src:/home/james/Projects/sat/drat-trim:$PATH"

(cd ../..; lake exe keller cnf $N $S --cnf $CNF --dsr $DSR --cube $CUBE)

dsr-trim -f $CNF $DSR $LSR --emit-valid-formula-to=$SB

cadical -q $SB $DRAT || true

drat-trim $SB $DRAT -w
