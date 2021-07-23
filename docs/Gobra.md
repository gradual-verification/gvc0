# Gobra API Usage

An outline of how Gobra uses the Viper/Silicon/Silver APIs. All code paths are relative to `<Gobra>/src/main/scala/viper/gobra/`.

## Overview

1. `GobraRunner.main` creates a verifier (`Gobra` object)
1. `Gobra.verify` parses the program, performs type-checking, translates it to Silver (`ProgramsImpl.translate`), and then verifies it (`Silicon.verify`)
1. `ProgramsImpl.translate` converts the Gobra AST to a Silver AST
1. `Silicon.verify` initializes Silicon and runs it over the Silver program AST
1. `viper.silicon.Silicon.fromPartialCommandLineArguments` is used to initialize Silicon

## `Gobra.scala`:

### Entry point (`GobraRunner.main`)

 * Reads config from command-line arguments
 * Creates a `GobraExecutionContext`
 * Creates a verifier (`GobraFrontend.createVerifier()`)
 * Calls `verifier.verify` with the config and execution context


### `GobraFrontend.createVerifier`
 * Creates a new `Gobra` object

### `Gobra.verify`
 * `performParsing`: Creates a Gobra AST `PPackage` object
 * `performTypeChecking`: Creates a Gobra-specific `TypeInfo` object
 * `performDesugaring`: Creates a Gobra AST `Program` object
 * `performInternalTransformations`: Creates a Gobra AST `Program` object
 * `performViperEncoding`: Creates a `BackendVerifier.Task` object, calls `viper.gobra.translator.Translator.translate`
 * `verifyAst`: Receives the Viper `Program` object
   * `.performVerification()`
   * `viper.gobra.backend.BackendVerifier.verify`

## `translator/Translator.scala`

### `Translator.translate`
 * Calls `ProgramsImpl.translate`

## `translator/implementations/translator/ProgramsImpl.scala`

### `ProgramsImpl.translate`
 * Receives a `viper.gobra.ast.Program`
 * Creates a `viper.silver.ast.Program` that includes domains, fields, predicates, functions, methods, and extensions

## `backend/BackendVerifier.scala`

### `BackendVerifier.verify`
 * Finds Z3 path
 * Finds Boogie path if using Carbon
 * Creates a backend from the config object (`config.backend.create`)
 * Creates a program ID (`_programID_{something}`)
 * Calls `verifier.verify`, passing it the program and execution context
 * Converts verification results

 ## `frontend/Config.scala`

 ### `Config.backend`
  * Checks for Silicon or Carbon backend
  * Defaults to `ViperBackends.SiliconBackend`

## `backend/ViperBackends.scala`

### `ViperBackends.SiliconBackend.create`
 * Creates a new `viper.gobra.backend.Silicon` object
 * Adds `--logLevel=ERROR`, `--disableCatchingExceptions`, `--enableMoreCompleteExhale`, and executable paths (for Z3) to the options

## `backend/Silicon.scala`

### `Silicon.verify`
 * Receives a program ID, config, reporter, Silver `Program`, and execution context
 * Creates a Silicon object (named `backend`) using `viper.silicon.Silicon.fromPartialCommandLineArguments` (needs args and a reporter)
 * Calls `backend.start`
 * Calls `backend.verify`
 * Calls `backend.stop`
 * Returns result of `backend.verify`