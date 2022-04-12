library(dplyr)
library(readr)
library(ggplot2)
library(tidyr)
library(grid)
library(gridExtra)
not_all_na <- function(x) any(!is.na(x))
dev.new(width=10, height=10, unit="in")
dest_dir <- "./stress/"

clean <- function(frame, status) {
    frame['mean'] <- frame['mean']/10 ** 9
    frame['median'] <- frame['median']/10 ** 9
    frame['Dynamic Verification'] <- status
    return(frame %>% select(where(not_all_na)) %>% drop_na())
}

plotlm <- function(name, data, form, r2val, hColor, factor) {

    annotations <- data.frame(
        xpos = c(-Inf),
        ypos =  c(Inf),
        hjustvar = c(-0.15),
        vjustvar = c(8)
    )
    p <- ggplot(data, aes(x, y)) +
        geom_point(col="#282828", size=.5, aes()) +
        geom_smooth(method='lm', formula=form, col = hColor) +
        xlab(expression("Workload ("~omega~")")) +
        ylab(paste("Time Elapsed (", factor, ")")) +
        ggtitle("") +
        theme_light() +
        theme(text = element_text(size=10, face="plain"), axis.title = element_text(size=8))
        
    labText <- paste("R^2: ", r2val)
    p + annotate(
            x=-Inf,
            y=Inf,
            hjust=-0.15,
            vjust=1.25,
            label=labText,
            size=3,
            geom="text",
            parse=TRUE,
        )
}

compile_individual <- function (df, model, name, hColor) {
    df <- data.frame(x=df$stress, y=df$median) %>% filter(x > 0)

    fit <- lm(model, data=df)
    fit_r2 <- summary(fit)$r.squared
    print(summary(fit))
    print(summary(fit))
    print(fit_r2)

    if(max(df$y) < 10**9){
        df$y <- df$y / (10**6)
        return(plotlm(name, df, model, fit_r2, hColor, "ms"))
    }else{
        df$y <- df$y / (10**9)
        return(plotlm(name, df, model, fit_r2, hColor, "sec"))
    }
}

compile <- function(dir, prefix, dynamic, base, hColor) {
    file.path(dir, paste(prefix, "_only_framing.csv", sep=""))

    full_dynamic <- read_csv(file.path(dir, paste(prefix, "_full_dynamic.csv", sep=""))) 
    fd_plot <- compile_individual(full_dynamic, dynamic, paste(prefix, "_full_dynamic"), hColor)

    only_framing <- read_csv(file.path(dir, paste(prefix, "_only_framing.csv", sep="")))
    of_plot <- compile_individual(only_framing, base, paste(prefix, "_only_framing"), hColor)

    unverified <- read_csv(file.path(dir, paste(prefix, "_unverified.csv", sep="")))
    uv_plot <- compile_individual(unverified, base, paste(prefix, "_unverified"), hColor)

    list(fd_plot, of_plot, uv_plot)
}
#green "#33A02C"
#purple "#6a3d9a"
# red "#de2d26"
bst_plots <- compile("./stress", "bst", y~I(x^2)*I(log(x)^2), y~x*log(x), "#33A02C")
composite_plots <- compile("./stress", "composite", y~I(x^2)*I(log(x)^2), y~x*I(log(x)^2), "#6a3d9a")
list_plots <- compile("./stress", "list", y~I(x^4), y~x, "#de2d26")

pl <- c(bst_plots, composite_plots, list_plots)
length(pl)

col.titles = c("Dynamic", "Only Framing", "Unverified")
row.titles = c("Binary Search Tree", "Composite", "Linked List")

# Add row titles
pl[1:3] = lapply(1:3, function(i) arrangeGrob(pl[[i]], left=row.titles[i], padding = unit(0.5, "line")))#textGrob(, gp=gpar(fontsize=8), rot=90)))

# Add column titles and lay out plots
grid.arrange(grobs=lapply(c(1,4,7), function(i) {
  arrangeGrob(grobs=pl[i:(i+2)], top=col.titles[i/3 + 1], ncol=1, padding = unit(0.5, "line"))
}), ncol=3)