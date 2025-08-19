INCCNF=$1
LOGS=$2
PROOFS=$3

JOBS=$(( $(nproc) - 1 ))

TOT_CUBES=$(cat $INCCNF | grep "^a " | wc -l)

for i in $(seq 1 $TOT_CUBES); do
    (
        cadical \
            <( (cat $INCCNF | grep -v "^a ")
               (cat $INCCNF | grep "^a " | tail -n+$i | head -n 1 | sed "s/a \|0$//g" | sed "s/ / 0 /g") ) \
            "$PROOFS/$i.drat" \
            > "$LOGS/$i.log"
    ) &

    echo -ne "\rStarted job $i/$TOT_CUBES"

    # allow to execute up to jobs in parallel
    if [[ $(jobs -r -p | wc -l) -ge $JOBS ]]; then
        # now there are $N jobs already running, so wait here for any job
        # to be finished so there is a place to start next one.
        wait -n
    fi
done

# no more jobs to be started but wait for pending jobs
# (all need to be finished)
wait

echo "\nall done"
