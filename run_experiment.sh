max=200
i=0

rm -f results.txt

while [ $i -lt $max ]; do
        i=$((i+1))
        prism -g "prism(cpairhmm_noalign), ms(align($i),Time)">out.txt
        table=$(cat out.txt | grep "tablespace" | cut -d: -f2)
        heap=$(cat out.txt | grep "heapspace" | cut -d: -f2)
        run=$(cat out.txt | grep "running time" | cut -d: -f2)
        echo "$i $run $table $heap" 
        echo "$i $run $table $heap" >> results.txt
done

rm -f out.txt
