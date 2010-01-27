#!/bin/sh

model=cpairhmm_globalstore_noannot
#model=cpairhmm_localstore_noannot
sequence_length=50
max_cardinality=$sequence_length
min_cardinality=0

rm -f results.txt
i=$min_cardinality
while [ $i -lt $max_cardinality ]; do
        i=$(($i+1))
        echo "constraint_checks([state_specific(global_cardinality([insert,delete],$i))])." > constraints.pl
        prism -g "prism($model), [testcphmm], ms(align($sequence_length),Time)">out.txt
        table=$(cat out.txt | grep "tablespace" | cut -d: -f2)
        heap=$(cat out.txt | grep "heapspace" | cut -d: -f2)
        run=$(cat out.txt | grep "running time" | cut -d: -f2)
        echo "$i $run $table $heap" 
        echo "$i $run $table $heap" >> results.txt
done

rm -f out.txt
