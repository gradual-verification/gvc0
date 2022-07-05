library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
library(tools)
library(purrr)

local_variance <- sample_variance("./local")
remote_variance <- sample_variance("./remote")

print(paste("Local variance: ", local_variance, "ns")
print(paste("Remote variance: ", remote_variance, "ns")

sample_variance <- function(base) {
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

    level_paths <- map_chr(level_paths, md5sum)
    if(length(unique(level_paths)) == 1){



    }else{
        print(paste("The samples in ", base, " differ by number and/or contents of paths.")
        quit(1)
    }
}




