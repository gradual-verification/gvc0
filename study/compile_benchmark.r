library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
options(dplyr.summarise.inform = FALSE)

# this script compiles all data produced by each of the three benchmark programs to produce the following files
# a single function, compile, processes all data for a single benchmark program. Adding a new benchmark program
# is as simple as adding an additional call to compile.
#
#./study
#   |- perf.csv      ----> full performance data for best/worst/median paths, including each baseline configuration
#   |- vcs.csv       ----> verification conditions present and statically eliminated for each partial spec
#   |- table.csv     ----> summary statistics comparing performance of gradual verification with the dynamic baseline
#   |- jumps.csv     ----> partial specs corresponding to 99th percentile minimum and maximum changes in runtime
#   |- bst
#       |- bst_min_jumps.csv            ---->  partial specs with 99th percentile decreases in runtime
#       |- bst_max_jumps.csv            ---->  partial specs with 99th percentile increases in runtime
#       |- bst_grad_vs_dyn.csv          ---->  summary statistics comparing gradual and dynamic verification configurations
#       |- bst_best_worst_median.csv    ---->  performance data for best, worst, and median paths
#       |- bst_vcs.csv                  ---->  verification condition data for each partial specification.
#   |- composite
#       |- ...
#   |- list
#       |- ...

# remove all rows containing N/A values
not_all_na <- function(x) any(!is.na(x))

# append the verification type indicator in a "verification" column and remove all rows with N/A values
clean <- function(frame, status) {
    frame["verification"] <- status
    # remove columns with all NA (extra comma), and then drop incomplete rows.
    return(frame %>% select(where(not_all_na)) %>% drop_na())
}

#Given the hash for a specification component, separate it into each of its fields and add each to an existing dataframe
unpack_context <- function(df, type, example) {
    df["context_name"] = NA
    df["context_type"] = NA
    df["component_type"] = NA
    for(row in 1:nrow(df)){
        #ex: p.sortedSegHelper.6.pred.default.74
        parts <- strsplit(df[[row, "component_added"]], "\\.")
        df[row,]["context_name"] <- parts[[1]][[2]]
        df[row,]["context_type"] <- parts[[1]][[4]]
        df[row,]["component_type"] <- parts[[1]][[5]] 
    }
    df['example'] <- example
    df['classification'] <- type
    return(df)
}



# for the summary statistics table, extract each relevant statistic and create a vector for a given row
create_summary_row <- function(data, stressLevel, prefix) {
    subset <- data %>% filter(stress == stressLevel)

    rows_lt_dyn <- subset %>% filter(diff_grad < 0)
    rows_gt_dyn <- subset %>% filter(diff_grad > 0)

    group_counts <- subset %>% group_by(path_id) %>% summarize(num_per_path = n())
    group_count <- group_counts$num_per_path %>% unique()

    percent_improved_grad_per_path <- subset %>%
        group_by(path_id) %>%
        filter(diff_grad < 0) %>%
        summarize(path_id, percent_steps_lt_dyn=n()/group_count[1] * 100) %>%
        distinct()

    steps_impr_mean <- round(mean(percent_improved_grad_per_path$percent_steps_lt_dyn), 1)
    steps_impr_max <- round(max(percent_improved_grad_per_path$percent_steps_lt_dyn), 1)
    steps_impr_min <- round(min(percent_improved_grad_per_path$percent_steps_lt_dyn), 1)
    steps_impr_sd <- round(sd(percent_improved_grad_per_path$percent_steps_lt_dyn), 1)

    percent_paths_complete <- nrow(percent_improved_grad_per_path %>% filter(percent_steps_lt_dyn == 100))/nrow(percent_improved_grad_per_path) * 100


    steps_lt_dyn <- round(nrow(rows_lt_dyn)/nrow(subset) * 100, 1)
    steps_gt_dyn <- round(nrow(rows_gt_dyn)/nrow(subset) * 100, 1)

    pdiff_grad_mean <- round(mean(subset$percent_diff_grad), 1)
    pdiff_grad_max <- round(max(subset$percent_diff_grad), 1)
    print(pdiff_grad_max)
    pdiff_grad_min <- round(min(subset$percent_diff_grad), 1)
    pdiff_grad_sd <- round(sd(subset$percent_diff_grad), 1)
    c(
        prefix,
        stressLevel,
        pdiff_grad_mean,
        pdiff_grad_sd,
        pdiff_grad_max, 
        pdiff_grad_min,

        steps_impr_mean,
        steps_impr_sd,
        steps_impr_max,
        steps_impr_min,
        percent_paths_complete
    )
}

# global performance data
perf_global <- data.frame()

# global verification condition data
vcs_global <- data.frame()

# contents of the summary statistics table
table_global <- data.frame()

# global data on increases and decreases in runtime over paths
jumps_global <- data.frame()


# the function "compile" calculates all statistics for an individual benchmark program, concatenating the results to each
# global dataframe defined above and writing them out into separate CSV files in a directory with the same name as
# the benchmark program.
compile <- function(dir, stressLevels) {
    print(paste("---[", basename(dir), "]---", sep=" "))

    # PREREQs
    # "permutation ID" - the unique identifier for a given partial specification
    # "runtime" - the median runtime taken from each of the measurements (iterations)

    # INITIALIZATION


    # levels.csv contains a mapping from permutation IDs to their path index, level index on that path,
    # and the hash for the specification component that was added at this step.
    levels_path <- file.path(dir, "levels.csv")
    levels <- read_csv(
            levels_path,
            show_col_types = FALSE
        )

#     metadata.csv maps permutation IDs to flags indicating which specification components are present in each permutation
#    meta_path <- file.path(dir, "metadata.csv")
#    meta <- read_csv(
#            meta_path,
#            show_col_types = FALSE
#        ) %>%
#       select(where(not_all_na))

    # a mapping from permutation IDs to profiling data from the verifier (conjuncts total, conjuncts eliminated)
    conj_path <- file.path(dir, "conjuncts.csv")
    conj <- read_csv(
            conj_path,
            show_col_types = FALSE
        ) %>%
        select(where(not_all_na))

    # a mapping from permutation IDs to summary statistics on their execution time at each specified workload value
    # for gradually verified, partial specifications
    perf_path <- file.path(dir, "dyn_perf_gradual.csv")
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
    perf_lattice$median <- perf_lattice$median / 10 ** 9

    # a mapping from permutation IDs to summary statistics on their execution time at each specified workload value
    # for the dynamic verification baseline
    full_dynamic_path <- file.path(dir, "dyn_perf_full_dynamic.csv")
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
    full_dynamic_lattice$median <- full_dynamic_lattice$median / 10 ** 9

    # a mapping from permutation IDs to summary statistics on their execution time at each specified workload value
    # for the "only framing" baseline
    only_framing_path <- file.path(dir, "dyn_perf_only_framing.csv")
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
    only_framing_lattice$median <- only_framing_lattice$median / 10 ** 9

    #DATA - [99th percentile jumps and decreases]
    # we calculate the 99th percentile changes in runtime, both increases and decreases, to determine which specification
    # components contribute the most to runtime overhead.
    # produces: "..._min_jumps.csv",
    # produces: "..._max_jumps.csv",

    #group gradual performance data by each path, ordered by level ID increasing
    #calculate the change in runtime and percent difference in runtime between adjacent levels
    path_level_characteristics <- perf_lattice %>%
        arrange(level_id) %>%
        group_by(path_id, stress) %>%
        mutate(diff = median - lag(median)) %>%
        mutate(pdiff = round((median - lag(median))/lag(median) * 100, 1)) %>%
        filter(level_id > 0) 

    #separate into increases and decreases in runtime
    decreases <- path_level_characteristics %>% filter(diff < 0)
    increases <- path_level_characteristics %>% filter(diff > 0)

    # find the threshold for 99th percentile increases and decreases
    quantile_max <- unname(quantile(increases$diff, c(.99)))[[1]]
    quantile_min <- -unname(quantile(abs(decreases$diff), c(.99)))[[1]]

    # find the increases and decreases that fell beyond each threshold
    quantile_min_jumps <- decreases %>% filter(diff <= quantile_min) %>% unpack_context("min", basename(dir))
    quantile_max_jumps <- increases %>% filter(diff >= quantile_max) %>% unpack_context("max", basename(dir))

    # transform the level ID into a percent indicating the proportion of specification components present.
    quantile_min_jumps$level_id <-round((quantile_min_jumps$level_id / max(quantile_min_jumps$level_id))*100, 1)
    quantile_max_jumps$level_id <-round((quantile_max_jumps$level_id / max(quantile_max_jumps$level_id))*100, 1)

    #bind data on jumps to the global set; then, save individual files for each benchmark
    jumps_global <<- bind_rows(jumps_global, quantile_min_jumps, quantile_max_jumps)

    quantile_min_jumps %>% write.csv(
            file.path(dir,paste(
                basename(dir),
                "_min_jumps.csv",
                sep = ""
            )),
            row.names = FALSE 
        )
    quantile_max_jumps %>% write.csv(
            file.path(dir,paste(
                basename(dir),
                "_max_jumps.csv",
                sep = ""
            )),
            row.names = FALSE 
        )


    # DATA - [Gradual Versus Dynamic Summary Statistics]
    # produces: "..._grad_vs_dyn.csv",

    #join performance data for gradual verification with dynamic verification, referring to dynamic runtime as "dyn_median"
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

    # calculate the magnitude and percent difference in runtime between gradual and dynamic verification
    g_vs_d$diff_grad <- g_vs_d$median - g_vs_d$dyn_median
    g_vs_d$percent_diff_grad <- g_vs_d$diff_grad / g_vs_d$dyn_median * 100


    # populate the table of summary statistics with entries for each selected stress level
    for (stressL in stressLevels)
    {
        sum_row <- create_summary_row(g_vs_d, stressL, basename(dir))
        table_global <<- rbind(table_global, sum_row)
    }
    g_vs_d %>% select(id, path_id, level_id, stress, diff_grad, percent_diff_grad) %>%
        write.csv(
            file.path(dir,paste(
                basename(dir),
                "_grad_vs_dyn.csv",
                sep = ""
            )),
            row.names = FALSE 
        )


    # DATA - [Best, Worst, and Median Paths]
    # produces: "..._best_worst_median.csv"

    # using the grouped performance data from earlier, calculate the minimum change, maximum change, average change,
    # and average overall runtime for each step contained within a given path, ordered by average runtime.
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

    # extract the three paths corresponding to the best, median, and wost average time elapsed across each step
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

    # join the data for steps along the best, worst, and median paths with full dynamic and only framing baselines,
    # providing complete performance data for every configuration along each of the three paths.
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

    # for the concatenated data, format time in milliseconds, specify the given benchmark program in an "example" column,
    # select only rows with the highest stress level, and format the level ID as a percentage toward a complete specification.
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
    # produces: "_vcs.csv"

    # join VCS table with information on the path and level id for each permutation,
    # formatting the level ID as a percentage toward completion and indicating the example that the data originates from
    # before concatenating to the global VCs dataframe.
    levels_index <- levels %>% select(id, path_id, level_id)

    conj_total <- conj %>% select(id, conjuncts_total) 
    colnames(conj_total) <- c("id", "VCs")
    conj_total["conj_type"] <- "total"

    conj_static <- conj %>% select(id, conjuncts_elim) 
    colnames(conj_static) <- c("id", "VCs")
    conj_static["conj_type"] <- "eliminated"

    conj_static_levels <- conj_static %>% inner_join(levels_index, by = c("id"))
    conj_total_levels <- conj_total %>% inner_join(levels_index, by = c("id"))
    conj_all <- bind_rows(
        conj_static_levels,
        conj_total_levels
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

args = commandArgs(trailingOnly=TRUE)
if (length(args)==0) {
  stop("A directory containing result directories for bst, list, and composite must be supplied.", call.=FALSE)
}
dir <- args[1]
compile(file.path(dir, "bst"), c(8,16,32))
#compile(file.path(dir, "list"), c(32, 64, 128))
#compile(file.path(dir, "composite"), c(4, 8, 16))

pg <- perf_global %>% write.csv(
        file.path(dir, "perf.csv"),
        row.names = FALSE
)

pvcs <- vcs_global %>% write.csv(
        file.path(dir, "vcs.csv"),
        row.names = FALSE
)

colnames(table_global) <- c("example", "workload", "mean_time", "sd_time", "max_time", "min_time", "mean_impr", "sd_impr", "max_impr", "min_impr", "complete_impr")
ptbl <- table_global %>% write.csv(
        file.path(dir, "table.csv"),
        row.names = FALSE
)

pjumps <- jumps_global %>% write.csv(
        file.path(dir, "jumps.csv"),
        row.names = FALSE
)