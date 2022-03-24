library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
library(gridExtra)
library(tikzDevice)

list_all <- read_csv("./stress/csv/list_all.csv")
bst_all <- read_csv("./stress/csv/bst_all.csv")
composite_all <- read_csv("./stress/csv/composite_all.csv")

list_none <- read_csv("./stress/csv/list_none.csv")
bst_none <- read_csv("./stress/csv/bst_none.csv")
composite_none <- read_csv("./stress/csv/composite_none.csv")

list <- data.frame(list_none['stress'], list_none['mean'], list_all['mean'])
bst <- data.frame(bst_none['stress'], bst_none['mean'], bst_all['mean'])
composite <- data.frame(composite_none['stress'], composite_none['mean'], composite_all['mean'])

colnames(list) <- c("stress", "Disabled", "Enabled")
colnames(bst) <- colnames(list)
colnames(composite) <- colnames(list)

list_plot <- list %>% gather(key, value, Enabled, Disabled) %>% ggplot(aes(x=stress, y=value, colour=key)) +
geom_line() +
xlab("Stress Factor") +
ylab("Runtime (sec.)") + guides(color=guide_legend(title="Dynamic Verification")) + ggtitle("List")

bst_plot <- bst %>% gather(key, value, Enabled, Disabled) %>% ggplot(aes(x=stress, y=value, colour=key)) +
geom_line() +
xlab("Stress Factor") +
ylab("Runtime (sec.)") + guides(color=guide_legend(title="Dynamic Verification")) + ggtitle("Binary Search Tree")

composite_plot <- composite %>% gather(key, value, Enabled, Disabled) %>% ggplot(aes(x=stress, y=value, colour=key)) +
geom_line() +
xlab("Stress Factor") +
ylab("Runtime (sec.)") + guides(color=guide_legend(title="Dynamic Verification")) + ggtitle("Composite")

grid.arrange(ggplotGrob(list_plot), ggplotGrob(bst_plot), ggplotGrob(composite_plot))