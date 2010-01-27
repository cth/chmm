d = Dir.open("runs/") 
numfiles = 0
entries_per_line = 0
experiments = []
d.each do |file|
        next if file == "." or file == ".."
        numfiles = numfiles + 1

        file_lines = []
        fd = File.open("runs/" + file) 
        fd.each do |line|
               line_entries = line.split
               entries_per_line = line_entries.length
               line_entries.map! { |entry| entry.to_i }
               file_lines << line_entries
        end
        fd.close
        experiments << file_lines 
end

number_of_experiments = experiments.length

avg_experiment = experiments.shift

experiments.each do |exp|
        0.upto(exp.length-1) do |run_i|
                run = exp[run_i]
                0.upto(run.length-1) do |datapoint_i|
                        avg_experiment[run_i][datapoint_i] = avg_experiment[run_i][datapoint_i] + run[datapoint_i]
                end
        end
end


0.upto(avg_experiment.length-1) do |run_i|
        run = avg_experiment[run_i]
        0.upto(run.length-1) do |datapoint_i|
                avg_experiment[run_i][datapoint_i] = avg_experiment[run_i][datapoint_i].to_f / number_of_experiments 
        end    
end

avg_experiment.each do |run|
        puts run.join(" ")
end
