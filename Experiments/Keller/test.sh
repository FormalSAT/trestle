N=6
S=32

DIR="$PWD/cnfs/g${N}_${S}"

mkdir -p $DIR

CNF="$DIR/keller.cnf"
SB_DSR="$DIR/symbreak.dsr"
CUBES="$DIR/cubes.dnf"

SB_LSR="$DIR/symbreak.lsr"
CNF_SB="$DIR/keller_sb.cnf"

ICNF="$DIR/keller_sb_cubes.icnf"
TAUTO="$DIR/keller_sb_cubes_tauto.cnf"

DRAT_SB="$DIR/keller_sb_proof.drat"
DRAT_SB_OPT="$DIR/keller_sb_proof_opt.drat"

DSR_FULL="$DIR/proof.dsr"
LSR_FULL="$DIR/proof.lsr"

set -e -x

(cd ../..; LEAN_ABORT_ON_PANIC=1 lake build keller srcheck)

PATH="$PWD/../../.lake/build/bin:$PATH"

# generate the CNF, the DSR proof, and the cubes
keller cnf $N $S --cnf $CNF --dsr $SB_DSR --cube $CUBES

# can also use the C encoder to generate CNF
#gcc Keller-encode.c && ./a.out $N $S > $CNF

# check the SR proof
time dsr-trim -f $CNF $SB_DSR $SB_LSR
#lsr-check $CNF $LSR
#srcheck $CNF $LSR

# append the SR proven clauses
keller append-sr-clauses --cnf $CNF --sr $SB_DSR --out $CNF_SB


USE_CUBES=true
if $USE_CUBES; then
  # combine CNF with cubes
  (echo "p inccnf"; grep -v "^p" $CNF_SB; cat $CUBES; echo "a 0") > $ICNF

  icadical --no-binary --skeletonIncremental $ICNF $DRAT_SB \
    || true
  #mkdir "$DIR/g${N}_${S}_sb_cube"
  #./run_par.sh $INC "$DIR/g${N}_${S}_sb_cube"
else
  # run it without the cubes
  cadical --forcephase=1 --scorefactor=500 $CNF_SB $DRAT_SB
fi

drat-trim $CNF_SB $DRAT_SB -l $DRAT_SB_OPT

(cat $SB_DSR $DRAT_SB_OPT | grep -v "^c" | grep -v "^d") > $DSR_FULL

dsr-trim $CNF $DSR_FULL $LSR_FULL
lsr-check $CNF $LSR_FULL
