library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)

args <- commandArgs(trailingOnly = TRUE)
if (length(args) < 2) {
    stop("Usage: Rscript ./data/compile.r [results dir] [output dir]", call. = FALSE)
}

results_dir <- args[1]
output_dir <- args[2]

static_performance2_path <- file.path(results_dir, "static_perf2.csv")
static_performance2 <- read_csv(
    static_performance2_path,
    show_col_types = FALSE
)

static_perf2_lattice <- static_performance2 %>%
  group_by(program_name) %>%
  mutate(percent_specified = round(level_id / max(level_id), 3) * 100) %>%
  mutate(mean = mean / 1E9) %>%
  select(program_name, percent_specified, mean)

static_perf2_lattice %>% 
  write.csv(
    file.path(output_dir, paste(
        "compiled_static_performance2.csv",
        sep = ""
    )),
    row.names = FALSE
)
                                  
