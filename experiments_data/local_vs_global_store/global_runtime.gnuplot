set xlabel "length of aligned sequences"
set ylabel "running time (seconds)"
plot "global_store.dat" using 1:2 with linespoint title "global non-tabled constraint store", x*x title "x^2"
set output "global_runtime.ps" 
set size 1.0, 0.6
set terminal postscript portrait enhanced mono dashed lw 1 "Helvetica" 14
replot
set terminal x11
set size 1,1


