N=6
S=32

DIR="$PWD/cnfs"

CNF="$DIR/g${N}_${S}.cnf"
DSR="$DIR/g${N}_${S}.dsr"
CUBES="$DIR/g${N}_${S}_cubes.dnf"

LSR="$DIR/g${N}_${S}.lsr"
SB="$DIR/g${N}_${S}_sb.cnf"
SB_DRAT="$DIR/g${N}_${S}_sb_proof.drat"

INC="$DIR/g${N}_${S}_sb_cube.icnf"
TAUTO="$DIR/g${N}_${S}_tauto.cnf"

set -e -x

(cd ../..; LEAN_ABORT_ON_PANIC=1 lake build keller srcheck)

PATH="$PWD/../../.lake/build/bin:$PATH"

# generate the CNF, the DSR proof, and the cubes
keller cnf $N $S --cnf $CNF --dsr $DSR --cube $CUBES

# can also use the C encoder to generate CNF
#gcc Keller-encode.c && ./a.out $N $S > $CNF

# check the SR proof
time dsr-trim -f $CNF $DSR $LSR
lsr-check $CNF $LSR
#srcheck $CNF $LSR

# append the SR proven clauses
keller append-sr-clauses --cnf $CNF --sr $DSR --out $SB

# combine CNF with cubes
(echo "p inccnf"; grep -v "^p" $SB; cat $CUBES) > $INC
# generate corresponding tautology check
keller negate-cubes --cnf $SB --cubes $CUBES --out $TAUTO

USE_CUBES=true
if $USE_CUBES; then
  # check that the cubes negated leads to tautology
  cadical $TAUTO || true

  mkdir "$DIR/g${N}_${S}_sb_cube"
  ./run_par.sh $INC "$DIR/g${N}_${S}_sb_cube"
else
  # run it without the cubes
  cadical --forcephase=1 --scorefactor=500 $SB $SB_DRAT
fi
