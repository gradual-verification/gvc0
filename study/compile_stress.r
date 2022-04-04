library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
not_all_na <- function(x) any(!is.na(x))

compile <- function(frame, status) {
    frame['mean'] <- frame['mean']/1000000000
    frame['Dynamic Verification'] <- status
    return(frame %>% select(where(not_all_na)) %>% drop_na())
}

list_all <- read_csv("./stress/list_all.csv")
list_all <- compile(list_all, 'Enabled')

bst_all <- read_csv("./stress/bst_all.csv")
bst_all <- compile(bst_all, 'Enabled')

composite_all <- read_csv("./stress/composite_all.csv")
composite_all <- compile(composite_all, 'Enabled')

list_none <- read_csv("./stress/list_none.csv")
list_none <- compile(list_none, 'Disabled')

bst_none <- read_csv("./stress/bst_none.csv")
bst_none <- compile(bst_none, 'Disabled')

composite_none <- read_csv("./stress/composite_none.csv")
composite_none <- compile(composite_none, 'Disabled')

list <- bind_rows(list_none, list_all) %>% select('Workload', 'Mean Time Elapsed (sec)', 'Dynamic Verification')
list['example'] = 'List'
bst <- bind_rows(bst_none, bst_all) %>% select('Workload', 'Mean Time Elapsed (sec)', 'Dynamic Verification')
bst['example'] = 'Binary Search Tree'
composite <- bind_rows(composite_none, composite_all) %>% select('Workload', 'Mean Time Elapsed (sec)', 'Dynamic Verification')
composite['example'] = 'Composite'

fit_data <- function(frame) {
    df <- data.frame(x=frame['stress'],y=frame['mean'])
    colnames(df) <- c("x", "y")
    fit = nls(y~a*x^2 + b*x + c, data = df, start=list(a=0, b=0, c=0))
    summary(fit)
}

print("-----[LIST]-----")
fit_data(list_all)
print("-----[COMPOSITE]-----")
fit_data(composite_all)
print("-----[BST]-----")
fit_data(bst_all)

all <- bind_rows(bst, list, composite)
names(all)[names(all) == 'stress'] <- "Workload (ω)"
names(all)[names(all) == 'mean'] <- "Mean Time Elapsed (sec)"
all %>% write.csv("./stress/stress.csv", row.names = FALSE)