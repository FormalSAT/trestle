INCCNF=$1
OUT=$2

JOBS=8

TOT_CUBES=$(cat $INCCNF | grep "^a " | wc -l)
LINES_PER_JOB=$(( ($TOT_CUBES+$JOBS-1) / $JOBS ))

echo "$TOT_CUBES cubes, $LINES_PER_JOB per job"

for j in $(seq 0 $(($JOBS-1))); do {
    START_IDX=$(( $LINES_PER_JOB * $j + 1))
    echo "job $j starts at $START_IDX"

    if [[ "$START_IDX" -lt "$TOT_CUBES" ]]; then
        (
            (cat $INCCNF | grep -v "^a ")
            (cat $INCCNF | grep "^a " | tail -n+$START_IDX | head -n $LINES_PER_JOB)
        ) | cadical > "$OUT/job_$j.log"
    fi
} &
done

wait
