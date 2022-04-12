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


unpack_context <- function(df) {
    df["context_name"] = NA
    df["context_type"] = NA
    df["component_type"] = NA
    for(row in 1:nrow(df)){
        #ex: p.sortedSegHelper.6.pred.default.74

        parts <- strsplit(df[[row, "component_added"]], "\\.")
    
        df[row,]$context_name <- parts[[1]][[2]]
        df[row,]$context_type <- parts[[1]][[4]]
        df[row,]$component_type <- parts[[1]][[5]] 
    }
    return(df)
}


create_summary_row <- function(data, stressLevel, prefix) {
    subset <- data %>% filter(stress == stressLevel)

    rows_lt_dyn <- subset %>% filter(diff_grad < 0)
    rows_gt_dyn <- subset %>% filter(diff_grad > 0)

    steps_lt_dyn <- round(nrow(rows_lt_dyn)/nrow(subset) * 100, 1)
    steps_gt_dyn <- round(nrow(rows_gt_dyn)/nrow(subset) * 100, 1)

    pdiff_grad_mean <- round(mean(subset$percent_diff_grad), 1)
    pdiff_grad_max <- round(max(subset$percent_diff_grad), 1)
    pdiff_grad_min <- round(min(subset$percent_diff_grad), 1)
    pdiff_grad_sd <- round(sd(subset$percent_diff_grad), 1)
    c(
        prefix,
        steps_lt_dyn,
        steps_gt_dyn, 
        pdiff_grad_mean, 
        pdiff_grad_max, 
        pdiff_grad_min, 
        pdiff_grad_sd
    )
}

perf_global <- data.frame()
vcs_global <- data.frame()
table_global <- data.frame()

compile <- function(dir, stressLevels) {

    # INITIALIZATION

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
            component_added,
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

    #DATA - [90th percentile jumps and decreases]

    path_level_characteristics <- perf_lattice %>%
        arrange(level_id) %>%
        group_by(path_id, stress) %>%
        mutate(diff = median - lag(median)) %>%
        filter(level_id > 0) 

    decreases <- path_level_characteristics %>% filter(diff < 0)
    increases <- path_level_characteristics %>% filter(diff > 0)

    quantile_max <- unname(quantile(increases$diff, c(.9)))[[1]]
    quantile_min <- -unname(quantile(abs(decreases$diff), c(.9)))[[1]]

    quantile_min_spikes <- decreases %>% filter(diff <= quantile_min) %>% unpack_context

    quantile_max_spikes <- increases %>% filter(diff >= quantile_max) %>% unpack_context

    quantile_min_spikes %>% write.csv(
            file.path(dir,paste(
                basename(dir),
                "_min_spikes.csv",
                sep = ""
            )),
            row.names = FALSE 
        )
    quantile_max_spikes %>% write.csv(
            file.path(dir,paste(
                basename(dir),
                "_max_spikes.csv",
                sep = ""
            )),
            row.names = FALSE 
        )


    # DATA - [Gradual Versus Dynamic Summary Statistics]
    dynamic_timing <- full_dynamic_lattice %>% 
        select(
            path_id,
            level_id,
            stress,
            median
        )
    names(dynamic_timing)[names(dynamic_timing) == 'median'] <- 'dyn_median'
    g_vs_d <- dynamic_timing %>% 
        inner_join(
            perf_lattice, 
            by = c("path_id", "level_id", "stress")
        )
    g_vs_d$diff_grad <- g_vs_d$median - g_vs_d$dyn_median
    g_vs_d$percent_diff_grad <- g_vs_d$diff_grad / g_vs_d$dyn_median * 100


    for (stressL in stressLevels)
    {
        sum_row <- create_summary_row(g_vs_d, stressL, basename(dir))
        table_global <<- rbind(table_global, sum_row)
    }

    g_vs_d %>% select(path_id, level_id, stress, diff_grad, percent_diff_grad) %>%
        write.csv(
            file.path(dir,paste(
                basename(dir),
                "_grad_vs_dyn.csv",
                sep = ""
            )),
            row.names = FALSE 
        )


    # DATA - [Best, Worst, and Median Paths]

    path_characteristics <- path_level_characteristics %>%
        group_by(path_id, stress) %>%
        summarize(
            time_elapsed = mean(median),
            max_spike = max(diff),
            min_spike = min(diff),
            diff_time_elapsed = mean(abs(diff)),
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

    all <- bind_rows(perf_joined, full_dynamic_joined, only_framing_joined)

    all$median <- all$median / 10 ** 6
    all["example"] <- basename(dir)
    max_stress <- max(all$stress)
    all <- all %>% filter(stress == max_stress)
    all$level_id <- all$level_id / max(all$level_id) * 100

    perf_global <<- bind_rows(perf_global, all)
    

    all %>% write.csv(
            file.path(dir,paste(
                basename(dir),
                "_best_worst_median.csv",
                sep = ""
            )),
            row.names = FALSE 
        )


    #DATA - [VCs Numbers Eliminated/Total]
    
    levels_index <- levels %>% select(id, path_id, level_id)
    conj <- conj %>% filter(conjuncts_elim < conjuncts_total)

    conj_total <- conj %>% select(id, conjuncts_total) 
    colnames(conj_total) <- c("id", "VCs")
    conj_total["conj_type"] <- "total"

    conj_static <- conj %>% select(id, conjuncts_elim) 
    colnames(conj_static) <- c("id", "VCs")
    conj_static["conj_type"] <- "eliminated"

    conj_all <- bind_rows(
        conj_static %>% inner_join(levels_index, on = c("id")),
        conj_total %>% inner_join(levels_index, on = c("id")),
    )
    #max_vcs <- max(conj$conjuncts_total)
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

compile("./results/bst", c(16, 32, 64))
compile("./results/list", c(16, 32, 64))
compile("./results/composite", c(8, 16, 32))

pg <- perf_global %>% write.csv(
        file.path("results/perf.csv"),
        row.names = FALSE
    )

pvcs <- vcs_global %>% write.csv(
        file.path("results/vcs.csv"),
        row.names = FALSE
    )

colnames(table_global) <- c("example", "<", ">", "mean", "max", "min", "sd")
ptbl <- table_global %>% write.csv(
        file.path("results/table.csv"),
        row.names = FALSE
)