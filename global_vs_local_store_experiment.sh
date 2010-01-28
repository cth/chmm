#!/bin/sh

#model=cpairhmm_globalstore_noannot
model=cpairhmm_localstore_noannot

constraints="constraint_checks([state_specific(local_cardinality([insert,delete],2,4))])."

max=12
i=0

echo $constraints > constraints.pl

rm -f results.txt

out=`tempfile`

while [ $i -lt $max ]; do
        i=$((i+1))
        prism -g "prism($model), [testcphmm], ms(align($i),Time)">$out
#        cat out.txt
        table=$(cat $out | grep "tablespace" | cut -d: -f2)
        heap=$(cat $out | grep "heapspace" | cut -d: -f2)
        run=$(cat $out | grep "running time" | cut -d: -f2)
        heap_and_table=$(($heap+$table))
        echo "$i $run $table $heap $heap_and_table" 
        echo "$i $run $table $heap $heap_and_table" >> results.txt
done

rm -f out.txt
