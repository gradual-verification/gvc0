library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)

not_all_na <- function(x) any(!is.na(x))
clean <- function(frame, status) {
    frame["verification"] <- status
    # remove columns with all NA (extra comma), and then drop incomplete rows.
    return(frame %>% select(where(not_all_na)) %>% drop_na())
}

perf_global <- data.frame()
vcs_global <- data.frame()

compile <- function(dir) {
    levels_path <- file.path(dir, "levels.csv")
    levels <- read_csv(
            levels_path,
            show_col_types = FALSE
        ) %>%
        select(where(not_all_na))

    meta_path <- file.path(dir, "metadata.csv")
    meta <- read_csv(
            meta_path,
            show_col_types = FALSE
        ) %>%
        select(where(not_all_na))

    conj_path <- file.path(dir, "conjuncts.csv")
    conj <- read_csv(
            conj_path,
            show_col_types = FALSE
        ) %>%
        select(where(not_all_na))


    perf_path <- file.path(dir, "perf.csv")
    perf <- read_csv(perf_path, show_col_types = FALSE) %>% clean("gradual")
    perf_lattice <- inner_join(
            levels,
            perf,
            by = c("id")
        ) %>%
        select(
            id,
            path_id,
            level_id,
            stress,
            median,
            verification
        )

    full_dynamic_path <- file.path(dir, "perf_full_dynamic.csv")
    full_dynamic <- read_csv(full_dynamic_path, show_col_types = FALSE) %>%
        clean("dynamic")
    full_dynamic_lattice <- inner_join(
            levels,
            full_dynamic,
            by = c("id")
        ) %>%
        select(
            id,
            path_id,
            level_id,
            stress,
            median,
            verification
        )
    
    only_framing_path <- file.path(dir, "perf_only_framing.csv")
    only_framing <- read_csv(only_framing_path, show_col_types = FALSE) %>%
        clean("framing")
    only_framing_lattice <- inner_join(
            levels,
            only_framing,
            by = c("id")
        ) %>%
        select(
            id,
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
        summarize(path_id = head(path_id, 1), classification = "best")
    worst <- path_characteristics %>%
        group_by(stress) %>%
        summarize(path_id = tail(path_id, 1), classification = "worst")
    median <- path_characteristics %>%
        group_by(stress) %>%
        filter(row_number() == ceiling(n() / 2)) %>%
        summarize(path_id = head(path_id, 1), classification = "median")

    path_classifications <- bind_rows(best, worst, median) %>% arrange(stress)

    perf_joined <- inner_join(
        perf_lattice,
        path_classifications,
        by = c("stress", "path_id")
    )

    full_dynamic_joined <- inner_join(
        full_dynamic_lattice,
        path_classifications,
        by = c("stress", "path_id")
    )

    only_framing_joined <- inner_join(
        only_framing_lattice,
        path_classifications,
        by = c("stress", "path_id") 
    )

    all <- bind_rows(perf_joined, full_dynamic_joined, only_framing_joined) %>% 
        filter(stress %in% c(16, 24, 32))

    all$median <- all$median / 10 ** 6
    all["example"] <- basename(dir)
    perf_global <<- bind_rows(perf_global, all)
    
    all %>% write.csv(
            file.path(dir,paste(
                basename(dir),
                "_best_worst_median.csv",
                sep = ""
            )),
            row.names = FALSE 
        )


    levels_index <- levels %>% select(id, path_id, level_id)
    conj <- conj %>% filter(conjuncts_elim < conjuncts_total)

    conj_total <- conj %>% select(id, conjuncts_total) 
    colnames(conj_total) <- c("id", "% VCs")
    conj_total["conj_type"] <- "total"

    conj_static <- conj %>% select(id, conjuncts_elim) 
    colnames(conj_static) <- c("id", "% VCs")
    conj_static["conj_type"] <- "eliminated"

    conj_all <- bind_rows(
        conj_static %>% inner_join(levels_index, on = c("id")),
        conj_total %>% inner_join(levels_index, on = c("id")),
    )
    max_vcs <- max(conj$conjuncts_total)

    conj_all["% VCs"] <- conj_all['% VCs'] / max_vcs * 100
    conj_all["example"] <- basename(dir)
    conj_all["% Specified"] <- conj_all$level_id / max(conj_all$level_id) * 100
    vcs_global <<- bind_rows(vcs_global, conj_all)

    conj_all %>% write.csv(
            file.path(dir,paste(
                basename(dir),
                "_vcs.csv",
                sep = ""
            )),
            row.names = FALSE 
        )
}

compile("./results/bst")
compile("./results/list")
compile("./results/composite")

perf_global %>% write.csv(
        file.path("results/perf.csv"),
        row.names = FALSE
    )

vcs_global %>% write.csv(
        file.path("results/vcs.csv"),
        row.names = FALSE
    )

problems()