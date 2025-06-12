N=6
S=32

DIR="$PWD/cnfs"

CNF="$DIR/g${N}_${S}.cnf"
DSR="$DIR/g${N}_${S}.dsr"
CUBES="$DIR/g${N}_${S}_cubes.icnf"

LSR="$DIR/g${N}_${S}.lsr"
SB="$DIR/g${N}_${S}_sb.cnf"
DRAT="$DIR/g${N}_${S}_sb_proof.drat"

TAUTO="$DIR/g${N}_${S}_tauto.cnf"

set -e -x

(cd ../..; LEAN_ABORT_ON_PANIC=1 lake build keller srcheck)

PATH="$PWD/../../.lake/build/bin:$PATH"

keller cnf $N $S --cnf $CNF --dsr $DSR --cube $CUBES

# check the SR proof
time dsr-trim -f $CNF $DSR $LSR
lsr-check $CNF $LSR
#srcheck $CNF $LSR

# make the CNF with SB clauses
keller append-sr-clauses --cnf $CNF --sr $DSR --out $SB

USE_CUBES=false
if $USE_CUBES; then
  # check that the cubes negated leads to tautology
  keller negate-cubes --cnf $SB --cubes $CUBES --out $TAUTO
  cadical $TAUTO || true

  # shuffle the cubes and start runnin em
  (echo "p inccnf"; grep -v "^p" $SB; cat $CUBES | shuf) |
      cadical
else
  cadical $SB $DRAT
fi
