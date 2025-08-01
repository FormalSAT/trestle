N=7
S=2

DIR="$PWD/cnfs/g${N}_${S}"

mkdir -p $DIR

CNF="$DIR/keller.cnf"
SB_DSR="$DIR/symbreak.dsr"
CUBES="$DIR/cubes.dnf"

SB_LSR="$DIR/symbreak.lsr"
CNF_SB="$DIR/keller_sb.cnf"

ICNF="$DIR/keller_sb_cubes.icnf"
TAUTO="$DIR/keller_sb_cubes_tauto.cnf"

SOLVER_LOG="$DIR/keller_sb.log"
DRAT_SB="$DIR/keller_sb.drat"
LRAT_SB="$DIR/keller_sb.lrat"

SKEL="$DIR/keller_sb.skel"

DSR_FULL="$DIR/proof.dsr"
LSR_FULL="$DIR/proof.lsr"

set -e -x

(cd ../..; LEAN_ABORT_ON_PANIC=1 lake build keller srcheck)

PATH="$PWD/../../.lake/build/bin:$PATH"

# generate the CNF, the DSR proof, and the cubes
keller cnf $N $S --cnf $CNF --dsr $SB_DSR --cube $CUBES

# check the SR proof
CHECK_SR=false
if [ "$CHECK_SR" = true ]; then
  time dsr-trim -f $CNF $SB_DSR $SB_LSR
  lsr-check $CNF $SB_LSR
  #srcheck $CNF $LSR
fi

# append the SR proven clauses
keller append-sr-clauses --cnf $CNF --sr $SB_DSR --out $CNF_SB

# 0 = lean cubing, 1 = proofix, 2 = skeleton
CUBE_SRC=0
if [ $CUBE_SRC -eq 1 ]; then
  python ../../../proofix/main.py \
    --cnf $CNF_SB \
    --icnf $CUBES \
    --cube-size 10 \
    --cutoff 500000 \
    --log $DIR/proofix.log \
    --cube-only --dynamic-depth 0
fi
if [ $CUBE_SRC -eq 2 ]; then
  # turn skeleton into cubes
  grep -v "^c" $SKEL | \
    sed 's/ 0 .*$//' | sed 's/^/a -/' | sed 's/ / -/g' | sed 's/--//g' | sed 's/$/ 0/' \
    > $CUBES
fi

# check cube tautology first
keller negate-cubes --cnf $CNF_SB --cubes $CUBES --out $TAUTO
cadical --quiet $TAUTO || (
  if [ $? -ne 20 ]; then
    false
  fi
)

# combine CNF with cubes
(echo "p inccnf"; grep -v "^p" $CNF_SB; cat $CUBES; echo "a 0") > $ICNF

RUN_PAR=true
if [ "$RUN_PAR" = true ]; then
  mkdir "$DIR/cubes"
  ./run_par.sh $ICNF "$DIR/cubes"
else
  (icadical --no-binary --skeletonIncremental $ICNF $DRAT_SB > $SOLVER_LOG) \
    || true
fi

exit
drat-trim $CNF_SB $DRAT_SB -L $LRAT_SB

# proof skeleton compression
lrat-skel -proof $LRAT_SB -nFormula $(  ) -nDRAT $( ) --from-LRAT \
  -nRatio 100 --write-seleton > $SKEL

# Combine into a single finalized proof
# does not work because dsr-trim has a bug (feature?)

(cat $SB_DSR $DRAT_SB_OPT | grep -v "^c") > $DSR_FULL

dsr-trim $CNF $DSR_FULL $LSR_FULL
lsr-check $CNF $LSR_FULL
