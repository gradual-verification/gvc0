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

DELIMITER //
CREATE PROCEDURE sp_gr_Program(IN p_name VARCHAR(255), IN p_hash VARCHAR(255), IN p_labels BIGINT UNSIGNED)
BEGIN
    IF (SELECT * FROM programs WHERE src_filename = p_name AND src_hash = p_hash AND num_labels = p_labels) THEN
        SELECT * FROM programs WHERE src_filename = p_name AND src_hash = p_hash AND num_labels = p_labels;
    ELSE
        INSERT INTO programs (src_filename, src_hash, num_labels) VALUES (p_name, p_hash, p_labels);
        SELECT * FROM programs WHERE id = (select LAST_INSERT_ID());
    END IF;
END //
DELIMITER ;


CREATE TABLE IF NOT EXISTS components
(
    id             SERIAL,
    program_id     BIGINT UNSIGNED                                                 NOT NULL,
    context_name   VARCHAR(255)                                                    NOT NULL,
    spec_type      ENUM ('post', 'assert', 'pre', 'unfold', 'fold', 'pred', 'inv') NOT NULL,
    spec_index     BIGINT UNSIGNED                                                 NOT NULL,
    expr_type      ENUM ('acc', 'pred', 'bool', 'rem_imp', 'abs')                  NOT NULL,
    expr_index     BIGINT UNSIGNED                                                 NOT NULL,
    component_date DATETIME                                                        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Component(IN p_id BIGINT UNSIGNED, IN p_cname VARCHAR(255),
                                 IN p_stype ENUM ('post', 'assert', 'pre', 'unfold', 'fold', 'pred', 'inv'),
                                 IN p_sindex BIGINT UNSIGNED, IN p_etype ENUM ('acc', 'pred', 'bool', 'rem_imp', 'abs'),
                                 IN p_eindex BIGINT UNSIGNED)
BEGIN
    IF (SELECT id
        FROM components
        WHERE program_id = p_id
          AND context_name = p_cname
          AND spec_type = p_stype
          AND spec_index = p_sindex
          AND expr_type = p_etype
          AND expr_index = p_eindex) THEN
        SELECT *
        FROM components
        WHERE program_id = p_id
          AND context_name = p_cname
          AND spec_type = p_stype
          AND spec_index = p_sindex
          AND expr_type = p_etype
          AND expr_index = p_eindex;
    ELSE
        INSERT INTO components (program_id, context_name, spec_type, spec_index, expr_type, expr_index)
        VALUES (p_id, p_cname, p_stype, p_sindex, p_etype, p_eindex);
        SELECT * FROM components WHERE id = (select LAST_INSERT_ID());
    END IF;
END //
DELIMITER ;

CREATE TABLE IF NOT EXISTS permutations
(
    id               SERIAL,
    program_id       BIGINT UNSIGNED NOT NULL,
    permutation_hash TEXT            NOT NULL,
    permutation_date DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Permutation(IN p_program_id BIGINT UNSIGNED, IN p_perm_hash TEXT)
BEGIN
    IF (SELECT * FROM permutations WHERE program_id = p_program_id AND permutation_hash = p_perm_hash) THEN
        SELECT * FROM permutations WHERE program_id = p_program_id AND permutation_hash = p_perm_hash;
    ELSE
        INSERT INTO permutations (program_id, permutation_hash) VALUES (p_program_id, p_perm_hash);
        SELECT * FROM permutations WHERE id = (select LAST_INSERT_ID());
    END IF;
END //


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
    component_id BIGINT UNSIGNED,
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

DELIMITER //
CREATE PROCEDURE sp_gr_Version(IN p_name VARCHAR(255))
BEGIN
    IF (SELECT * FROM versions WHERE version_name = p_name) THEN
        SELECT * FROM versions WHERE version_name = p_name;
    ELSE
        INSERT INTO versions (version_name) VALUES (p_name);
        SELECT * FROM programs WHERE id = (select LAST_INSERT_ID());
    END IF;
END //

DELIMITER ;


CREATE TABLE IF NOT EXISTS hardware
(
    id            SERIAL,
    hardware_name VARCHAR(255) UNIQUE NOT NULL,
    hardware_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Hardware(IN p_name VARCHAR(255))
BEGIN
    IF (SELECT * FROM hardware WHERE hardware_name = p_name) THEN
        SELECT * FROM hardware WHERE hardware_name = p_name;
    ELSE
        INSERT INTO hardware (hardware_name) VALUES (p_name);
        SELECT * FROM hardware WHERE id = (select LAST_INSERT_ID());
    END IF;
END //
DELIMITER ;

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
    stress           INTEGER,
    iter             INTEGER,
    performance_date DATETIME DEFAULT CURRENT_TIMESTAMP,
    mode_measured    ENUM ('translation', 'verification', 'instrumentation', 'compilation', 'exec_gradual', 'exec_framing', 'exec_dynamic'),

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
