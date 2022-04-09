library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)

compile <- function(frame, status) {
    frame["verification"] <- status
    # remove columns with all NA (extra comma), and then drop incomplete rows.
    return(frame %>% select(where(not_all_na)) %>% drop_na())
}
not_all_na <- function(x) any(!is.na(x))
args <- commandArgs(trailingOnly = TRUE)

if (length(args) != 1) {
      stop("A directory must be specified.", call = FALSE)
}

levels_path <- file.path(args[1], "levels.csv")
levels <- read_csv(
        levels_path,
        show_col_types = FALSE
    ) %>%
    select(where(not_all_na))

meta_path <- file.path(args[1], "metadata.csv")
meta <- read_csv(
        meta_path,
        show_col_types = FALSE
    ) %>%
    select(where(not_all_na))

perf_path <- file.path(args[1], "perf.csv")
perf <- read_csv(perf_path, show_col_types = FALSE) %>% compile("Gradual")
perf_lattice <- inner_join(
        levels,
        perf,
        by = c("id")
    ) %>%
    select(
        path_id,
        level_id,
        stress,
        median,
        verification
    )

full_dynamic_path <- file.path(args[1], "perf_full_dynamic.csv")
full_dynamic <- read_csv(full_dynamic_path, show_col_types = FALSE) %>%
    compile("Dynamic")
full_dynamic_lattice <- inner_join(
        levels,
        full_dynamic,
        by = c("id")
    ) %>%
    select(
        path_id,
        level_id,
        stress,
        median,
        verification
    )

only_framing_path <- file.path(args[1], "perf_only_framing.csv")
only_framing <- read_csv(only_framing_path, show_col_types = FALSE) %>%
    compile("Only Framing")
only_framing_lattice <- inner_join(
        levels,
        only_framing,
        by = c("id")
    ) %>%
    select(
        path_id,
        level_id,
        stress,
        median,
        verification
    )

path_characteristics <- perf_lattice %>%
    arrange(level_id) %>%
    group_by(path_id, stress) %>%
    mutate(diff_time_elapsed = median - lag(median)) %>%
    filter(level_id > 0) %>%
    group_by(path_id, stress) %>%
    summarize(
        time_elapsed = mean(median),
        diff_time_elapsed = mean(abs(diff_time_elapsed)),
        highest_positive_spike = max(diff_time_elapsed),
        highest_negative_spike = min(diff_time_elapsed),
        .groups = "keep"
    ) %>%
    arrange(time_elapsed)

best <- path_characteristics %>%
    group_by(stress) %>%
    summarize(path_id = head(path_id, 1), classification = "Best")
worst <- path_characteristics %>%
    group_by(stress) %>%
    summarize(path_id = tail(path_id, 1), classification = "Worst")
median <- path_characteristics %>%
    group_by(stress) %>%
    filter(row_number() == ceiling(n() / 2)) %>%
    summarize(path_id = head(path_id, 1), classification = "Median")

path_classifications <- bind_rows(best, worst, median) %>% arrange(stress)

perf_joined <- inner_join(
    perf_lattice,
    path_classifications,
    by = c("stress", "path_id")
)

base_perf_joined <- inner_join(
    base_perf_lattice,
    path_classifications,
    by = c("stress", "path_id")
)

all <- bind_rows(perf_joined, base_perf_joined) %>% 
    filter(stress %in% c(16, 24, 32))


all$median <- all$median / 10 ** 6
all["Example"] <- basename(args[1])
all %>% write.csv(
            file.path(args[1],paste(
                basename(args[1]),
                "_best_worst_median.csv",
                sep = ""
            )),
            row.names = FALSE
        )