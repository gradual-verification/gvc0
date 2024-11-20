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

sp2 <- static_performance2 %>%
  group_by(program_name) %>%
  mutate(percent_specified = round(level_id / max(level_id), 3) * 100) %>%
  mutate(mean = mean / 1E9)

static_perf2_lattice <- sp2 %>%
  select(permutation_id, program_name, percent_specified, mean)


path_level_characteristics <- sp2 %>%
  mutate(diff = mean - lag(mean)) %>%
  select(permutation_id, program_name, percent_specified, mean, diff, spec_type, expr_type)

increases <- path_level_characteristics %>% filter(diff > 0)
decreases <- path_level_characteristics %>% filter(diff < 0)

quantile_max <- unname(quantile(increases$diff, c(.99)))[[1]]
quantile_min <- -unname(quantile(abs(decreases$diff), c(.99)))[[1]]

quantile_min_jumps <- decreases %>% filter(diff <= quantile_min)
quantile_min_jumps['classification'] <- "min"

quantile_max_jumps <- increases %>% filter(diff >= quantile_max)
quantile_max_jumps['classification'] <- "max"

jumps_global <<- bind_rows(quantile_min_jumps, quantile_max_jumps)

static_perf2_lattice %>% 
  write.csv(
    file.path(output_dir, paste(
        "compiled_static_performance2.csv",
        sep = ""
    )),
    row.names = FALSE
)

jumps_global %>%
    write.csv(
        file.path(output_dir, "static2_jumps.csv"),
        row.names = FALSE
    )
