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
  select(permutation_id, program_name, percent_specified, mean)

list_752 <- static_perf2_lattice %>%
  filter(program_name == "list", percent_specified == 75.2) %>%
  select(mean)

list_761 <- static_perf2_lattice %>%
  filter(program_name == "list", percent_specified == 76.1) %>%
  select(mean)

list_826 <- static_perf2_lattice %>%
  filter(program_name == "list", percent_specified == 82.6) %>%
  select(mean)

list_835 <- static_perf2_lattice %>%
  filter(program_name == "list", percent_specified == 83.5) %>%
  select(mean)

list_862 <- static_perf2_lattice %>%
  filter(program_name == "list", percent_specified == 86.2) %>%
  select(mean)

list_872 <- static_perf2_lattice %>%
  filter(program_name == "list", percent_specified == 87.2) %>%
  select(mean)

print("75.2 -> 76.1")
print(summary(list_752))
print(summary(list_761))
print("98 percentile")
print(quantile(list_761$mean, c(.98)))
print("99 percentile")
print(quantile(list_761$mean, c(.99)))
print("82.6 -> 83.5")
print(summary(list_826))
print(summary(list_835))
print("98 percentile")
print(quantile(list_835$mean, c(.98)))
print("99 percentile")
print(quantile(list_835$mean, c(.99)))
print("86.2 -> 87.2")
print(summary(list_862))
print(summary(list_872))
print("98 percentile")
print(quantile(list_872$mean, c(.98)))
print("99 percentile")
print(quantile(list_872$mean, c(.99)))

static_perf2_lattice %>% 
  write.csv(
    file.path(output_dir, paste(
        "compiled_static_performance2.csv",
        sep = ""
    )),
    row.names = FALSE
)
                                  
