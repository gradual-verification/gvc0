library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
compile <- function(frame, status) {
    frame['Mean Time Elapsed (sec)'] <- frame['mean']/1000000000
    frame['Workload'] <- frame['stress']
    # remove columns with all NA (extra comma), and then drop incomplete rows.
    return(frame %>% select(where(not_all_na)) %>% drop_na())
}
not_all_na <- function(x) any(!is.na(x))
args = commandArgs(trailingOnly=TRUE)
if(length(args) != 1){
      stop("A directory must be specified.", call.=FALSE)
}

levels_path <- file.path(args[1], "levels.csv")
levels <- read_csv(levels_path) %>% select(where(not_all_na))

meta_path <- file.path(args[1], "metadata.csv")
meta <- read_csv(meta_path) %>% select(where(not_all_na))

perf_path <- file.path(args[1], "perf.csv")
perf <- read_csv(perf_path) %>% compile("gradual")

base_perf_path <- file.path(args[1], "baseline_perf.csv")
base_perf <- read_csv(base_perf_path) %>% compile("dynamic")

perf_lattice <- inner_join(levels, perf, by=c("id"))
max_perf_lattice <- perf_lattice %>% slice_max(stress)
max_perf_lattice %>% write.csv(file.path(args[1],"max_perf_lattice.csv"), row.names = FALSE)

base_perf_lattice <- inner_join(levels, base_perf, by=c("id"))

