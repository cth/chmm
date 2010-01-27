#!/bin/sh
# Use for running the same experiment multiple times. For instance, 
# ./many_runs 10 runs/dataitem "./run_experiment

num_runs=$1
prefix=$2
targetscript=$3

i=1
while [ $i -le $1 ]; do
        echo "running experiment: $i"
        $3 > $prefix$i
        i=$(($i+1))
done

