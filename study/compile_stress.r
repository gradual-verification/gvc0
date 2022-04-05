library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
not_all_na <- function(x) any(!is.na(x))

compile <- function(frame, status) {
    frame['mean'] <- frame['mean']/10 ** 9
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
bst_none
list <- bind_rows(list_none, list_all)
list['Example'] = 'List'
bst <- bind_rows(bst_none, bst_all)
bst['Example'] = 'Binary Search Tree'
composite <- bind_rows(composite_none, composite_all)
composite['Example'] = 'Composite'

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
colnames(all) <- c("Workload (ω)", "iter", "Median Time Elapsed (sec)", "Mean Time Elapsed (sec)", "stdev", "min", "max", "Dynamic Verification", "Example")
all %>% write.csv("./stress/stress.csv", row.names = FALSE)