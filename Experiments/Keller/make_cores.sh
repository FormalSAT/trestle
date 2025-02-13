THREADS=12
CUBES=38584

for ((t=0; t<$THREADS; t++))
do
  echo "Thread $t"
  (
    for ((i=38479; i>=10000; i--))
    do
      if [ $(($i % $THREADS)) -eq $t ]; then
        echo "Starting $i"
        lake --log-level=ERROR exe keller cnf 7 64 --cube "$i" "cube_$i.cnf" 1> /dev/null
        cadical -q "cube_$i.cnf" "proof_$i.drat" 1> /dev/null
        if [[ $? -ne 20 ]]; then
          echo "cadical failed: $i"
        else
          drat-trim "cube_$i.cnf" "proof_$i.drat" -c "cores/core_$i.cnf" -w 1> /dev/null
        fi
        rm "cube_$i.cnf" "proof_$i.drat"
      fi
    done
  ) &
done

wait
