library(dplyr)
library(readr)
list_all <- read_csv("./stress/csv/list_all.csv")
bst_all <- read_csv("./stress/csv/bst_all.csv")
composite_all <- read_csv("./stress/csv/composite_all.csv")

list_none <- read_csv("./stress/csv/list_all.csv")
bst_none <- read_csv("./stress/csv/bst_all.csv")
composite_none <- read_csv("./stress/csv/composite_all.csv")

list_none['name'] = 'none'
list_all['name'] = 'all'
bst_none['name'] = 'none'
bst_all['name'] = 'all'
composite_none['name'] = 'none'
composite_all['name'] = 'all'

list <- rbind(list_none, list_all) %>% select(name, stress, mean)
bst <- rbind(bst_none, bst_all) %>% select(name, stress, mean)
composite <- rbind(composite_none, composite_all) %>% select(name, stress, mean)

list %>% write.csv(., file="./stress/csv/list.csv")
bst %>% write.csv(., file="./stress/csv/bst.csv")
composite %>% write.csv(., file="./stress/csv/composite.csv")
