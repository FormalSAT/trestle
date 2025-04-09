N=7
S=64

DIR="$PWD/cnfs"

CNF="$DIR/g${N}_${S}.cnf"
DSR="$DIR/g${N}_${S}.dsr"
CUBES="$DIR/g${N}_${S}_cubes.icnf"

LSR="$DIR/g${N}_${S}.lsr"
SB="$DIR/g${N}_${S}_sb.cnf"

TMPDIR="tmp"

set -e -x

PATH="/home/james/Projects/sat/dsr-trim/src:/home/james/Projects/sat/drat-trim:$PATH"
#PATH="/home/james/Projects/dsr-trim/src:/home/james/Projects/drat-trim:$PATH"

(cd ../..; LEAN_ABORT_ON_PANIC=1 lake exe keller cnf $N $S --cnf $CNF --dsr $DSR --cube $CUBES)

time dsr-trim -f $CNF $DSR $LSR --emit-valid-formula-to=$SB
lsr-check $CNF $LSR

if [ -d $TMPDIR ]
then
    rm -r $TMPDIR
fi

mkdir $TMPDIR

line_number=0
while IFS= read -r cube; do
    TMP="tmp/cube$line_number.cnf"
    cat <(echo "p inccnf") <(grep -v "^p" $SB) <(echo "$cube") > $TMP
    cadical $TMP
    rm $TMP

    line_number=$(( $line_number + 1 ))
done < "$CUBES"

rmdir $TMPDIR
