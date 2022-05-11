# Quantitative Study Resources
This directory is intended to be used to contain all benchmarking output from the verifier, R scripts for compiling it
into formats that are easy to work with, and JSON files for rendering graphs using Vega Lite.

    .
    ├── benchmarks              # an uncommitted, but necessary directory for storing raw benchmarking output from the verifier.
    ├── results                 # compiled CSV files for the performance lattice of each benchmark program, produced by ./compile_benchmark.r
        ├── bst
        ├── composite
        ├── list
    ├── stress                  # compiled CSV files for stress testing data, produced by compile_stress.r
        ├── bst
        ├── composite
        ├── list
    ├── vega                    # JSON definitions for visualizations to be used with the output data in Vega Lite.
    ├── compile_benchmark.r     # A script that compiles data produces by the --benchmark mode
    └── compile_stress.r        # A script that compiles data produced by the --stress mode

To be able to use `compile_benchmark.r`, the directory `results` must be created with subdirectories for each benchmark program. Similarly,
`stress` and its subdirectories are necessary to use `compile_stress.r`. 

