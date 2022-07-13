library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
library(tools)
library(purrr)
library(matrixStats)


percent_stdev <- function(levels_path, perf_paths) {
    get_max_stress <- function(tb) {
        max(tb$stress)
    }

    read_silenced <- function(path){
        read_csv(path, show_col_types = FALSE)
    }
    base <- read_csv(levels_path, show_col_types = FALSE) %>% select(id)
    read_perf <- map(perf_paths, read_silenced)
    max_stress_perf <- map(read_perf, get_max_stress)
    if(length(unique(max_stress_perf)) != 1){
        print(paste("The samples differ by number and/or contents of paths."))
        quit()
    }else{
        perf_column_names <- c()
        for(i in 1:length(perf_paths)){
            perf_data <- read_csv(perf_paths[[i]], show_col_types = FALSE)
            perf_data <- perf_data %>% select(id, stress, median) %>% filter(stress == max(stress))
            colnames(perf_data) <- c("id", "stress", i)
            perf_column_names <- append(perf_column_names, paste(i))
            base <- base %>% inner_join(perf_data[,-2], by=c("id"))
        }
        base$mean <- apply(base[,perf_column_names], FUN = mean, na.rm = T, MARGIN = 1)
        base$stdev <- apply(base[,perf_column_names], FUN = sd, na.rm = T, MARGIN = 1)
        base$percent_stdev <- (base$stdev / base$mean * 100)
        mean(base$percent_stdev)
    }
}

sample_percent_stdev <- function(base) {
    sample_dirs <- list.dirs(base, recursive = FALSE)

    level_paths <- c()
    gradual_paths <- c()
    framing_paths <- c()
    dynamic_paths <- c()


    for (s_dir in sample_dirs) {
        level_paths <- append(level_paths, file.path(s_dir, "levels.csv"))
        gradual_paths <- append(gradual_paths, file.path(s_dir, "dyn_perf_gradual.csv"))
        framing_paths <- append(framing_paths, file.path(s_dir, "dyn_perf_only_framing.csv"))
        dynamic_paths <- append(dynamic_paths, file.path(s_dir, "dyn_perf_full_dynamic.csv"))
    }

    level_path_hashes <- map_chr(level_paths, md5sum)

    if(length(unique(level_path_hashes)) == 1){
        lp <- level_paths[[1]]
        round(abs(mean(percent_stdev(lp, gradual_paths), percent_stdev(lp, framing_paths), percent_stdev(lp, dynamic_paths))))
    }else{
        print(paste("The samples in ", base, " differ by number and/or contents of paths."))
        quit()
    }
}
local_variance <- sample_percent_stdev("./local")
remote_variance <- sample_percent_stdev("./remote")
print(paste("Local average % of mean for stdev: ", local_variance, "%", sep=""))
print(paste("Remote average stdev % of mean for stdev: ", remote_variance, "%", sep=""))
