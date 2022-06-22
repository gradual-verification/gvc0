library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
options(dplyr.summarise.inform = FALSE)

compile <- function(dir, stressLevels) {
    print(paste("---[", basename(dir), "]---", sep=" "))
    # INITIALIZATION
    # levels.csv contains a mapping from permutation IDs to their path index, level index on that path,
    # and the hash for the specification component that was added at this step.
    levels_path <- file.path(dir, "levels.csv")
    levels <- read_csv(
            levels_path,
            show_col_types = FALSE
        )

    comp_path <- file.path(dir, "compilation_perf_gradual.csv")
    comp <- read_csv(
            comp_path,
            show_col_types = FALSE
       )

    conj_path <- file.path(dir, "conjuncts.csv")
    conj <- read_csv(
            conj_path,
            show_col_types = FALSE
        )

    translation_path <- file.path(dir, "translation_perf.csv")
    translation <- read_csv(
            translation_path,
            show_col_types = FALSE
        ) %>% select(id, mean)
    translation['stage'] <- "translation"

    instrumentation_path <- file.path(dir, "instrumentation_perf.csv")
    instrumentation <- read_csv(
            instrumentation_path,
            show_col_types = FALSE
        ) %>% select(id, mean)
    instrumentation['stage'] <- "instrumentation"

    verification_path <- file.path(dir, "verification_perf.csv")
    verification <- read_csv(
            verification_path,
            show_col_types = FALSE
        ) %>% select(id, mean)
    verification['stage'] <- "verification"

    all <- bind_rows(verification, instrumentation, translation)

    all['example'] <- basename(dir)

    all <- all %>% inner_join(conj, by=c("id")) %>% inner_join(levels, by="id") %>%
        select(mean, stage, example, conjuncts_total, conjuncts_elim, path_id, level_id)
    
    all$mean <- all$mean / (10**6)
    all['level_id'] <- all['level_id'] / max(all['level_id']) * 100

    static_perf_global <<- bind_rows(
        static_perf_global,
        all
    )

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

    comp["example"] <- basename(dir)
    comp_by_level <- comp %>% inner_join(levels, by=c("id")) %>% select(level_id, path_id, median, example)
    comp_by_level$median <- comp_by_level$median / (10**6)
    comp_by_level["level_id"] <- comp_by_level$level_id / max(comp_by_level$level_id) * 100
    comp_global <<- bind_rows(comp_global, comp_by_level)
}
# global performance data
static_perf_global <- data.frame()
vcs_global <- data.frame()
comp_global <- data.frame()

compile("./results-static/bst")
compile("./results-static/composite")

pg <- static_perf_global %>% write.csv(
        file.path("results-static/static_perf.csv"),
        row.names = FALSE
)
pvcs <- vcs_global %>% write.csv(
        file.path("results-static/vcs.csv"),
        row.names = FALSE
)
pcomp <- comp_global %>% write.csv(
        file.path("results-static/comp_global.csv"),
        row.names = FALSE
)
