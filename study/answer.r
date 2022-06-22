library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
options(dplyr.summarise.inform = FALSE)

levels_path <- file.path("./perf_full.csv")
data <- read_csv(
        levels_path,
        show_col_types = FALSE
    )

component_keys <- data %>% filter(example == "list", verification=="gradual", stress==128, classification=="worst") %>% select(path_id, level_id, component_added, classification) %>% unique()
dynamic_without_component <- data %>% filter(example == "list", verification=="gradual", stress==128, classification=="worst") %>% select(path_id, level_id, median)
concatenated <- dynamic_without_component %>% inner_join(component_keys, by=c("level_id", "path_id")) %>% arrange(level_id)
path_10 <- concatenated %>% filter(path_id==2) %>% mutate(diff = median - lag(median)) %>% arrange(desc(level_id))

print(path_10)


jumps_path <- file.path("./jumps_full.csv")
jumps_list <- read_csv(
        jumps_path,
        show_col_types = FALSE
    )
