library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
options(dplyr.summarise.inform = FALSE)
options(warn = 2)
not_all_na <- function(x) any(!is.na(x))
not_any_na <- function(x) all(!is.na(x))

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
        reframe(path_id, percent_steps_lt_dyn=n()/group_count[1] * 100) %>%
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

args <- commandArgs(trailingOnly = TRUE)
if (length(args) < 2) {
    stop("Usage: Rscript ./data/compile.r [results dir] [output dir]", call. = FALSE)
}

results_dir <- args[1]
output_dir <- args[2]

print(paste("Compiling Directory", (results_dir), "]---", sep = " "))

path_index_path <- file.path(results_dir, "path_index.csv")
path_index <- read_csv(
    path_index_path,
    show_col_types = FALSE
)

program_index_path <- file.path(results_dir, "program_index.csv")
program_index <- read_csv(
    program_index_path,
    show_col_types = FALSE
)

measurement_type_index_path <- file.path(results_dir, "measurement_type_index.csv")
mt_index <- read_csv(
    measurement_type_index_path,
    show_col_types = FALSE
)
mt_id_for <- function(name) {
    mt_index[which(mt_index$measurement_type == name), ]$measurement_type_id[1]
}
static_performance_path <- file.path(results_dir, "static_perf.csv")
static_performance <- read_csv(
    static_performance_path,
    show_col_types = FALSE
)

dynamic_performance_path <- file.path(results_dir, "dynamic_perf.csv")
dynamic_performance <- read_csv(
    dynamic_performance_path,
    show_col_types = FALSE
) %>% select(program_id, permutation_id, measurement_type_id, stress, iter, median)

print("Creating performance lattice...")
perf_lattice <- inner_join(
    path_index,
    dynamic_performance,
    by = c("program_id", "permutation_id")
) %>% inner_join(mt_index, by = c("measurement_type_id")) %>% group_by(program_id)

perf_lattice$median <- perf_lattice$median / 10**6

print("Creating gradual subset performance lattice...")
gradual_lattice <- perf_lattice %>% filter(measurement_type_id == mt_id_for("gradual"))

print("Creating dynamic subset performance lattice...")
dynamic_lattice <- perf_lattice %>% filter(measurement_type_id == mt_id_for("dynamic"))

print("Creating framing subset performance lattice...")
framing_lattice <- perf_lattice %>% filter(measurement_type_id == mt_id_for("framing"))

# global performance data
perf_global <- data.frame()


# global verification condition data
vcs_global <- data.frame()

# contents of the summary statistics table
table_global <- data.frame(matrix(ncol = 11, nrow = 0))
colnames(table_global) <- c(
    "prefix",
    "stress", 
    "pdiff_grad_mean",
    "pdiff_grad_sd",
    "pdiff_grad_max", 
    "pdiff_grad_min",
    "steps_impr_mean",
    "steps_impr_sd",
    "steps_impr_max",
    "steps_impr_min",
    "percent_paths_complete"
)

# global data on increases and decreases in runtime over paths
jumps_global <- data.frame()

analyze <- function(pid, pname) {

    g <- gradual_lattice %>% filter(program_id == pid) %>%
        select(
            program_id,
            permutation_id, 
            path_id, 
            level_id, 
            median, 
            stress
        )
    print(paste("# of unique programs:", length(g$permutation_id %>% unique())))

    names(g)[names(g) == 'median'] <- 'gradual_median'
    d <- dynamic_lattice %>% filter(program_id == pid) %>%
        select(
            program_id,
            permutation_id, 
            path_id, 
            level_id, 
            median, 
            stress
        )
    names(d)[names(d) == 'median'] <- 'dynamic_median'

    f <- framing_lattice %>% filter(program_id == pid) %>% 
        select(
            program_id,
            permutation_id, 
            path_id, 
            level_id, 
            median, 
            stress
        )
    names(f)[names(f) == 'median'] <- 'framing_median'
    g_vs <- inner_join(g, d, by = c("path_id", "level_id", "stress", "permutation_id", "program_id"))
    g_vs <- inner_join(g_vs, f, by = c("path_id", "level_id", "stress", "permutation_id", "program_id"))
    path_level_characteristics <- g_vs %>%
        arrange(level_id) %>%
        group_by(path_id, stress) %>%
        mutate(diff = gradual_median - lag(gradual_median)) %>%
        mutate(pdiff = round((gradual_median - lag(gradual_median))/lag(gradual_median) * 100, 1)) %>%
        filter(level_id > 0)
    
    #separate into increases and decreases in runtime
    decreases <- path_level_characteristics %>% filter(diff < 0)
    increases <- path_level_characteristics %>% filter(diff > 0)
    # find the threshold for 99th percentile increases and decreases
    quantile_max <- unname(quantile(increases$diff, c(.99)))[[1]]
    quantile_min <- -unname(quantile(abs(decreases$diff), c(.99)))[[1]]

    # find the increases and decreases that fell beyond each threshold
    quantile_min_jumps <- decreases %>% filter(diff <= quantile_min)
    quantile_min_jumps['example'] <- program_name
    quantile_min_jumps['classification'] <- "min"

    quantile_max_jumps <- increases %>% filter(diff >= quantile_max)
    quantile_max_jumps['example'] <- program_name
    quantile_max_jumps['classification'] <- "max"

    # transform the level ID into a percent indicating the proportion of specification components present.
    quantile_min_jumps$completion_percentage <-round((quantile_min_jumps$level_id / max(quantile_min_jumps$level_id))*100, 1)
    quantile_max_jumps$completion_percentage <-round((quantile_max_jumps$level_id / max(quantile_max_jumps$level_id))*100, 1)

    #bind data on jumps to the global set; then, save individual files for each benchmark
    jumps_global <<- bind_rows(jumps_global, quantile_min_jumps, quantile_max_jumps)
    g_vs$diff_grad <- g_vs$gradual_median - g_vs$dynamic_median
    g_vs$percent_diff_grad <- g_vs$diff_grad / g_vs$dynamic_median * 100

    stressLevels <- g_vs$stress %>% unique()
    # populate the table of summary statistics with entries for each selected stress level
    for (stressL in stressLevels)
    {
        sum_row <- create_summary_row(g_vs, stressL, program_name)
        table_global[nrow(table_global)+1,] <<- sum_row
    }

    # using the grouped performance data from earlier, calculate the minimum change, maximum change, average change,
    # and average overall runtime for each step contained within a given path, ordered by average runtime.
    path_characteristics <- path_level_characteristics %>%
        group_by(path_id, stress) %>%
        summarize(
            time_elapsed = mean(gradual_median),
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
    gradual_joined <- inner_join(
        gradual_lattice,
        path_classifications,
        by = c("stress", "path_id")
    )
    dynamic_joined <- inner_join(
        dynamic_lattice,
        path_classifications,
        by = c("stress", "path_id")
    )
    framing_joined <- inner_join(
        framing_lattice,
        path_classifications,
        by = c("stress", "path_id")
    )

    all <- bind_rows(gradual_joined, dynamic_joined, framing_joined) %>%
        select(
            program_id,
            path_id,
            level_id,
            measurement_type,
            stress,
            iter,
            median,
            classification,
        )
    all["example"] <- program_name

    max_stress <- max(all$stress)

    all <- all %>% filter(stress == max_stress)

    all$level_id <- all$level_id / max(all$level_id) * 100  

    perf_global <<- bind_rows(perf_global, all)
}


for (row in 1:nrow(program_index)) {
    program_name <- program_index[row, "program_name"] %>% pull()
    program_id <- program_index[row, "program_id"] %>% pull()

    print(paste("Analyzing data for", program_name))
    analyze(program_id, program_name)
}

pg <- perf_global %>% write.csv(
        file.path(output_dir, "compiled_dynamic_performance.csv"),
        row.names = FALSE
)

tg <- table_global %>% write.csv(
        file.path(output_dir, "compiled_table.csv"),
        row.names = FALSE
)

jg <- jumps_global %>% inner_join(path_index, by=c("program_id","permutation_id","path_id","level_id")) %>%
    write.csv(
        file.path(output_dir, "compiled_jumps.csv"),
        row.names = FALSE
    )

print("Creating static performance lattice...")

static_perf_lattice <- inner_join(
    path_index,
    static_performance,
    by = c("permutation_id")
) %>%
    inner_join(program_index, by = c("program_id")) %>%
    group_by(program_name) %>%
    mutate(percent_specified = round(level_id / max(level_id), 3) * 100)

conj_elim <- static_perf_lattice %>% 
    select(
        program_name, 
        permutation_id, 
        path_id, 
        level_id, 
        conj_elim, 
        percent_specified
    )

conj_elim["conj_type"] <- "Eliminated"
conj_elim["VCs"] <- conj_elim$conj_elim

conj_total <- static_perf_lattice %>% 
    select(
        program_name, 
        permutation_id, 
        path_id, 
        level_id, 
        conj_total, 
        percent_specified
    )

conj_total["conj_type"] <- "Total"
conj_total["VCs"] <- conj_total$conj_total

static_perf_lattice <- bind_rows(conj_elim, conj_total) %>% 
    select(
        program_name,
        permutation_id,
        path_id, 
        level_id,
        conj_type,
        VCs, 
        percent_specified
    )


static_perf_lattice %>% write.csv(
    file.path(output_dir, paste(
        "compiled_static_performance.csv",
        sep = ""
    )),
    row.names = FALSE
)
perf_lattice %>% ungroup() %>%
    inner_join(program_index, by=c("program_id")) %>%
    select(program_name, level_id, stress, median, measurement_type) %>%
    write.csv(file.path(output_dir, "full_dynamic_performance.csv"), row.names = FALSE)
