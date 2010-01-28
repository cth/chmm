set log y
set xlabel "length of aligned sequences"
set ylabel "running time (seconds)"
plot "average20_local.dat" using 1:2 with lines title "local tabled constraint store", "average20_global.dat" using 1:2 with lines title "global non-tabled constraint store", x*x title "x^2" with lines
set output "global_vs_local_running_time.ps" 
set size 1.0, 0.6
set terminal postscript portrait enhanced mono dashed lw 1 "Helvetica" 14
replot
set terminal x11
set size 1,1


