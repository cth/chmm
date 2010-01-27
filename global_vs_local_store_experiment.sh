#!/bin/sh

model=cpairhmm_globalstore_noannot
#model=cpairhmm_localstore_noannot

constraints="constraint_checks([state_specific(local_cardinality([insert,delete],2,4))])."

max=100
i=0

echo $constraints > constraints.pl

rm -f results.txt

while [ $i -lt $max ]; do
        i=$((i+1))
        prism -g "prism($model), [testcphmm], ms(align($i),Time)">out.txt
#        cat out.txt
        table=$(cat out.txt | grep "tablespace" | cut -d: -f2)
        heap=$(cat out.txt | grep "heapspace" | cut -d: -f2)
        run=$(cat out.txt | grep "running time" | cut -d: -f2)
        heap_and_table=$(($heap+$table))
        echo "$i $run $table $heap $heap_and_table" 
        echo "$i $run $table $heap $heap_and_table" >> results.txt
done

rm -f out.txt
