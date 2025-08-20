DIR=$1

TS="$(date +'%Y-%m-%d_%H:%M:%S')"
SUMMARY_FILE="$DIR/summary_$TS.log"
STATS_FILE="$DIR/stats_$TS.log"

grep "total process time since initialization" -R $DIR/logs/ |\
  sed 's/.*logs\/\([0-9]\+\).*: *\([0-9.]\+\) .*/\2\t\1/' |\
  sort -rn > $SUMMARY_FILE

( echo "Statistics for $DIR at $TS"
  echo "Num. Cubes: $(cat $SUMMARY_FILE | wc -l)"
  echo "Tot. Time (s): $(awk 'BEGIN {s=0.0} {s+=$1} END {printf "%f", s}' $SUMMARY_FILE)"
  echo "Hardest cubes:"
  while read line; do
    T=$(echo $line | awk '{print $1}')
    N=$(echo $line | awk '{print $2}')
    CUBE=$(cat $DIR/cubes.dnf | sed "${N}q;d")
    echo -e "$N\t$T\t\t$CUBE"
  done < <(head $SUMMARY_FILE)
) > $STATS_FILE
