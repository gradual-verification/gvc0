DROP DATABASE IF EXISTS gvc0;
CREATE DATABASE gvc0;
USE gvc0;
CREATE TABLE IF NOT EXISTS programs
(
    id           SERIAL,
    src_filename VARCHAR(255)        NOT NULL,
    src_hash     VARCHAR(255) UNIQUE NOT NULL,
    num_labels   BIGINT UNSIGNED     NOT NULL,
    program_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id)
);
CREATE TABLE IF NOT EXISTS components
(
    id             SERIAL,
    program_id     BIGINT UNSIGNED                                                 NOT NULL,
    fn_name        VARCHAR(255)                                                    NOT NULL,
    spec_type      ENUM ('post', 'assert', 'pre', 'unfold', 'fold', 'pred', 'inv') NOT NULL,
    spec_index     BIGINT UNSIGNED                                                 NOT NULL,
    expr_type      ENUM ('acc', 'pred_inst', 'bool', 'rem_imp')                    NOT NULL,
    expr_index     BIGINT UNSIGNED                                                 NOT NULL,
    component_date DATETIME                                                        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);
CREATE TABLE IF NOT EXISTS permutations
(
    id               SERIAL,
    program_id       BIGINT UNSIGNED NOT NULL,
    permutation_hash TEXT            NOT NULL,
    permutation_date DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);
CREATE TABLE IF NOT EXISTS paths
(
    id         SERIAL,
    path_hash  TEXT            NOT NULL,
    program_id BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (id, program_id),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);
CREATE TABLE IF NOT EXISTS steps
(
    id           SERIAL,
    perm_id      BIGINT UNSIGNED NOT NULL,
    path_id      BIGINT UNSIGNED NOT NULL,
    level_id     BIGINT UNSIGNED NOT NULL,
    component_id BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (id, perm_id, path_id, level_id),
    FOREIGN KEY (perm_id) REFERENCES permutations (id),
    FOREIGN KEY (path_id) REFERENCES paths (id)
);

CREATE TABLE IF NOT EXISTS versions
(
    id           SERIAL,
    version_name VARCHAR(255) UNIQUE NOT NULL,
    version_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id)
);
CREATE TABLE IF NOT EXISTS hardware
(
    id            SERIAL,
    hardware_name VARCHAR(255) UNIQUE NOT NULL,
    hardware_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id)
);
CREATE TABLE IF NOT EXISTS conjuncts
(
    id              SERIAL,
    perm_id         BIGINT UNSIGNED NOT NULL,
    version_id      BIGINT UNSIGNED NOT NULL,
    hardware_id     BIGINT UNSIGNED NOT NULL,
    conj_total      BIGINT UNSIGNED NOT NULL,
    conj_eliminated BIGINT UNSIGNED NOT NULL,
    conj_date       DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    FOREIGN KEY (perm_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id)
);
CREATE TABLE IF NOT EXISTS performance
(
    id               SERIAL,
    program_id       BIGINT UNSIGNED NOT NULL,
    version_id       BIGINT UNSIGNED NOT NULL,
    hw_id            BIGINT UNSIGNED NOT NULL,
    performance_date DATETIME DEFAULT CURRENT_TIMESTAMP,
    mode_measured    ENUM ('translation', 'verification', 'instrumentation', 'compilation', 'exec_gradual', 'exec_framing', 'exec_dynamic'),
    stress           INTEGER,
    iter             INTEGER,
    ninety_fifth     DOUBLE PRECISION,
    fifth            DOUBLE PRECISION,
    median           DOUBLE PRECISION,
    mean             DOUBLE PRECISION,
    stdev            DOUBLE PRECISION,
    minimum          DOUBLE PRECISION,
    maximum          DOUBLE PRECISION,
    FOREIGN KEY (program_id) REFERENCES programs (id),
    FOREIGN KEY (hw_id) REFERENCES hardware (id),
    FOREIGN KEY (version_id) REFERENCES versions (id)
);
