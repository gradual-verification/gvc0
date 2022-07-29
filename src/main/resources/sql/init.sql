DROP TABLE IF EXISTS global_configuration;
DROP TABLE IF EXISTS static_performance;
DROP TABLE IF EXISTS dynamic_performance;
DROP TABLE IF EXISTS measurements;
DROP TABLE IF EXISTS dynamic_measurement_types;
DROP TABLE IF EXISTS errors;
DROP TABLE IF EXISTS benchmark_membership;
DROP TABLE IF EXISTS benchmarks;
DROP TABLE IF EXISTS steps;
DROP TABLE IF EXISTS permutations;
DROP TABLE IF EXISTS components;
DROP TABLE IF EXISTS paths;
DROP TABLE IF EXISTS programs;
DROP TABLE IF EXISTS nicknames;
DROP TABLE IF EXISTS hardware;
DROP TABLE IF EXISTS versions;

DROP PROCEDURE IF EXISTS sp_gr_Program;
DROP PROCEDURE IF EXISTS sp_ReservePermutation;
DROP PROCEDURE IF EXISTS sp_gr_Permutation;
DROP PROCEDURE IF EXISTS sp_gr_Component;
DROP PROCEDURE IF EXISTS sp_gr_Error;
DROP PROCEDURE IF EXISTS sp_gr_Hardware;
DROP PROCEDURE IF EXISTS sp_gr_Version;
DROP PROCEDURE IF EXISTS sp_gr_Nickname;
DROP PROCEDURE IF EXISTS sp_gr_Program;
DROP PROCEDURE IF EXISTS sp_UpdateStatic;

DROP EVENT IF EXISTS delete_reserved_permutations;

CREATE TABLE IF NOT EXISTS global_configuration
(
    id              ENUM ('1') DEFAULT '1',
    timeout_minutes BIGINT UNSIGNED NOT NULL,
    max_paths       BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (id)
);

INSERT INTO global_configuration (timeout_minutes, max_paths)
VALUES (60, 4);


CREATE TABLE IF NOT EXISTS programs
(
    id           SERIAL,
    src_filename VARCHAR(255)        NOT NULL,
    src_hash     VARCHAR(255) UNIQUE NOT NULL,
    num_labels   BIGINT UNSIGNED     NOT NULL,
    program_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    UNIQUE KEY contents (src_filename, src_hash, num_labels)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Program(IN p_name VARCHAR(255), IN p_hash VARCHAR(255), IN p_labels BIGINT UNSIGNED,
                               OUT p_id BIGINT UNSIGNED)
BEGIN
    INSERT IGNORE INTO programs (src_filename, src_hash, num_labels) VALUES (p_name, p_hash, p_labels);
    SELECT id
    INTO p_id
    FROM programs
    WHERE src_filename = p_name
      AND src_hash = p_hash
      AND num_labels = p_labels;
END //
DELIMITER ;

CREATE TABLE IF NOT EXISTS components
(
    id             SERIAL,
    program_id     BIGINT UNSIGNED NOT NULL,
    context_name   VARCHAR(255)    NOT NULL,
    spec_type      VARCHAR(255)    NOT NULL,
    spec_index     BIGINT UNSIGNED NOT NULL,
    expr_type      VARCHAR(255)    NOT NULL,
    expr_index     BIGINT UNSIGNED NOT NULL,
    component_date DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    UNIQUE KEY contents (program_id, spec_type, spec_index, expr_type, expr_index),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Component(IN p_id BIGINT UNSIGNED, IN p_cname VARCHAR(255),
                                 IN p_stype VARCHAR(255),
                                 IN p_sindex BIGINT UNSIGNED, IN p_etype VARCHAR(255),
                                 IN p_eindex BIGINT UNSIGNED,
                                 OUT c_id BIGINT UNSIGNED)
BEGIN
    INSERT IGNORE INTO components (program_id, context_name, spec_type, spec_index, expr_type, expr_index)
    VALUES (p_id, p_cname, p_stype, p_sindex, p_etype, p_eindex);
    SELECT id
    INTO c_id
    FROM components
    WHERE program_id = p_id
      AND context_name = p_cname
      AND spec_type = p_stype
      AND spec_index = p_sindex
      AND expr_type = p_etype
      AND expr_index = p_eindex;
END //
DELIMITER ;

CREATE TABLE IF NOT EXISTS permutations
(
    id               SERIAL,
    program_id       BIGINT UNSIGNED NOT NULL,
    permutation_hash BLOB            NOT NULL,
    permutation_date DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    UNIQUE KEY contents (program_id, permutation_hash),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Permutation(IN p_program_id BIGINT UNSIGNED, IN p_perm_hash BLOB, OUT p_id BIGINT UNSIGNED)
BEGIN
    SELECT id
    INTO p_id
    FROM permutations
    WHERE program_id = p_program_id
      AND permutation_hash = p_perm_hash;
    IF ((SELECT p_id) IS NULL) THEN
        INSERT INTO permutations (program_id, permutation_hash) VALUES (p_program_id, p_perm_hash);
        SELECT LAST_INSERT_ID() INTO p_id;
    END IF;
END //
DELIMITER ;


CREATE TABLE IF NOT EXISTS paths
(
    id         SERIAL,
    path_hash  BLOB            NOT NULL,
    program_id BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (id, program_id),
    FOREIGN KEY (program_id) REFERENCES programs (id)
);

CREATE TABLE IF NOT EXISTS steps
(
    id             SERIAL,
    permutation_id BIGINT UNSIGNED NOT NULL,
    path_id        BIGINT UNSIGNED NOT NULL,
    level_id       BIGINT UNSIGNED NOT NULL,
    component_id   BIGINT UNSIGNED,
    PRIMARY KEY (id, permutation_id, path_id, level_id),
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (path_id) REFERENCES paths (id)
);

CREATE TABLE IF NOT EXISTS versions
(
    id           SERIAL,
    version_name VARCHAR(255) UNIQUE NOT NULL,
    version_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id, version_name)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Version(IN p_name VARCHAR(255), OUT v_id BIGINT UNSIGNED)
BEGIN
    INSERT IGNORE INTO versions (version_name) VALUES (p_name);
    SELECT id INTO v_id FROM versions WHERE version_name = p_name;
END //

DELIMITER ;


CREATE TABLE IF NOT EXISTS hardware
(
    id            SERIAL,
    hardware_name VARCHAR(255) UNIQUE NOT NULL,
    hardware_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id, hardware_name)
);


DELIMITER //
CREATE PROCEDURE sp_gr_Hardware(IN p_name VARCHAR(255), OUT h_id BIGINT UNSIGNED)
BEGIN
    INSERT IGNORE INTO hardware (hardware_name) VALUES (p_name);
    SELECT id INTO h_id FROM hardware WHERE hardware_name = p_name;
END //
DELIMITER ;

CREATE TABLE IF NOT EXISTS nicknames
(
    id            SERIAL,
    nickname      VARCHAR(255) UNIQUE NOT NULL,
    nickname_date DATETIME            NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id, nickname)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Nickname(IN p_nname VARCHAR(255), OUT n_id BIGINT UNSIGNED)
BEGIN
    INSERT IGNORE INTO nicknames (nickname) VALUES (p_nname);
    SELECT id INTO n_id FROM nicknames WHERE nickname = p_nname;
END //
DELIMITER ;


CREATE TABLE IF NOT EXISTS benchmarks
(
    id             SERIAL,
    benchmark_name VARCHAR(255),
    benchmark_desc TEXT,
    PRIMARY KEY (id, benchmark_name)
);
INSERT INTO benchmarks (benchmark_name, benchmark_desc)
VALUES ('default', 'the first path generated for each program.');

CREATE TABLE IF NOT EXISTS benchmark_membership
(
    benchmark_id   BIGINT UNSIGNED NOT NULL,
    permutation_id BIGINT UNSIGNED NOT NULL,
    FOREIGN KEY (benchmark_id) REFERENCES benchmarks (id),
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    PRIMARY KEY (benchmark_id, permutation_id)
);

CREATE TABLE IF NOT EXISTS dynamic_measurement_types
(
    id               SERIAL,
    measurement_type VARCHAR(255) NOT NULL UNIQUE,
    PRIMARY KEY (id)
);

INSERT INTO dynamic_measurement_types (measurement_type)
VALUES ('gradual');
INSERT INTO dynamic_measurement_types (measurement_type)
VALUES ('framing');
INSERT INTO dynamic_measurement_types (measurement_type)
VALUES ('dynamic');

CREATE TABLE IF NOT EXISTS measurements
(
    id           SERIAL,
    iter         INTEGER,
    ninety_fifth DOUBLE PRECISION,
    fifth        DOUBLE PRECISION,
    median       DOUBLE PRECISION,
    mean         DOUBLE PRECISION,
    stdev        DOUBLE PRECISION,
    minimum      DOUBLE PRECISION,
    maximum      DOUBLE PRECISION,
    PRIMARY KEY (id)
);

CREATE TABLE IF NOT EXISTS errors
(
    id                   SERIAL,
    error_desc           TEXT                  DEFAULT NULL,
    error_date           DATETIME     NOT NULL DEFAULT CURRENT_TIMESTAMP,
    error_type           VARCHAR(255) NOT NULL,
    time_elapsed_seconds BIGINT UNSIGNED,
    PRIMARY KEY (id)
);

CREATE TABLE IF NOT EXISTS static_performance
(
    permutation_id          BIGINT UNSIGNED NOT NULL,
    version_id              BIGINT UNSIGNED NOT NULL,
    hardware_id             BIGINT UNSIGNED NOT NULL,
    nickname_id             BIGINT UNSIGNED NOT NULL,
    translation_perf_id     BIGINT UNSIGNED NOT NULL,
    verification_perf_id    BIGINT UNSIGNED NOT NULL,
    instrumentation_perf_id BIGINT UNSIGNED NOT NULL,
    compilation_perf_id     BIGINT UNSIGNED NOT NULL,
    conj_total              BIGINT UNSIGNED NOT NULL,
    conj_eliminated         BIGINT UNSIGNED NOT NULL,
    error_id                BIGINT UNSIGNED DEFAULT NULL,
    FOREIGN KEY (translation_perf_id) REFERENCES measurements (id),
    FOREIGN KEY (verification_perf_id) REFERENCES measurements (id),
    FOREIGN KEY (instrumentation_perf_id) REFERENCES measurements (id),
    FOREIGN KEY (compilation_perf_id) REFERENCES measurements (id),
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (nickname_id) REFERENCES nicknames (id),
    FOREIGN KEY (error_id) REFERENCES errors (id),
    PRIMARY KEY (permutation_id, hardware_id, version_id, nickname_id)
);

DELIMITER //
CREATE PROCEDURE sp_UpdateStatic(IN vid BIGINT UNSIGNED, IN hid BIGINT UNSIGNED, IN nid BIGINT UNSIGNED,
                                 IN perm_id BIGINT UNSIGNED, IN tr_id BIGINT UNSIGNED, IN vf_id BIGINT UNSIGNED,
                                 IN inst_id BIGINT UNSIGNED, IN cp_id BIGINT UNSIGNED, IN total_cond BIGINT UNSIGNED,
                                 IN elim_cond BIGINT UNSIGNED)
BEGIN
    SELECT @ex = version_id,
           @ex_tr = translation_perf_id,
           @ex_vf = verification_perf_id,
           @ex_inst = instrumentation_perf_id,
           @ex_cp = compilation_perf_id
    FROM static_performance
    WHERE version_id = vid
      AND hardware_id = hid
      AND permutation_id = perm_id
      AND nickname_id = nid
        FOR
    UPDATE;
    IF ((SELECT @ex) IS NOT NULL) THEN
        UPDATE static_performance
        SET translation_perf_id     = tr_id,
            verification_perf_id    = vf_id,
            instrumentation_perf_id = inst_id,
            compilation_perf_id     = cp_id,
            conj_total              = total_cond,
            conj_eliminated         = elim_cond,
            error_id                = NULL
        WHERE version_id = vid
          AND hardware_id = hid
          AND permutation_id = perm_id
          AND nickname_id = nid;

        DELETE FROM measurements WHERE id = (SELECT @ex_tr);
        DELETE FROM measurements WHERE id = (SELECT @ex_vf);
        DELETE FROM measurements WHERE id = (SELECT @ex_inst);
        DELETE FROM measurements WHERE id = (SELECT @ex_cp);
    ELSE
        INSERT INTO static_performance (permutation_id, version_id, hardware_id, nickname_id, translation_perf_id,
                                        verification_perf_id, instrumentation_perf_id, compilation_perf_id, conj_total,
                                        conj_eliminated, error_id)
        VALUES (perm_id, vid, hid, nid, tr_id, vf_id, inst_id, cp_id, total_cond, elim_cond, NULL);
    END IF;
END //
DELIMITER ;

CREATE TABLE IF NOT EXISTS dynamic_performance
(
    permutation_id           BIGINT UNSIGNED NOT NULL,
    version_id               BIGINT UNSIGNED NOT NULL,
    hardware_id              BIGINT UNSIGNED NOT NULL,
    nickname_id              BIGINT UNSIGNED NOT NULL,
    stress                   INTEGER         NOT NULL,
    dynamic_measurement_type BIGINT UNSIGNED NOT NULL,
    measurement_id           BIGINT UNSIGNED          DEFAULT NULL,
    last_updated             DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    error_id                 BIGINT UNSIGNED          DEFAULT NULL,
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (nickname_id) REFERENCES nicknames (id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (dynamic_measurement_type) REFERENCES dynamic_measurement_types (id),
    FOREIGN KEY (measurement_id) REFERENCES measurements (id),
    FOREIGN KEY (error_id) REFERENCES errors (id),
    PRIMARY KEY (permutation_id, version_id, hardware_id, nickname_id, stress, dynamic_measurement_type)
);

DELIMITER //
CREATE PROCEDURE sp_ReservePermutation(IN vid BIGINT UNSIGNED, IN hid BIGINT UNSIGNED, IN nnid BIGINT UNSIGNED,
                                       IN workload BIGINT UNSIGNED,
                                       OUT perm_id BIGINT UNSIGNED,
                                       OUT missing_mode BIGINT UNSIGNED)
BEGIN

    SELECT @found_perm_id := permutations.id,
           @found_missing_mode := dynamic_measurement_types.id
    FROM permutations
             CROSS JOIN (SELECT vid, hid, workload) AS identity
             CROSS JOIN dynamic_measurement_types
             LEFT OUTER JOIN dynamic_performance dp ON dp.permutation_id = permutations.id
        AND dp.version_id = identity.vid AND dp.hardware_id = identity.hid AND dp.stress = identity.workload
        AND dp.dynamic_measurement_type = dynamic_measurement_types.id
    WHERE dp.permutation_id IS NULL
    LIMIT 1
    FOR
    UPDATE OF permutations SKIP LOCKED;

    IF ((SELECT @found_perm_id) IS NOT NULL) THEN
        INSERT INTO dynamic_performance (permutation_id, version_id, hardware_id, nickname_id, stress,
                                         dynamic_measurement_type)
        VALUES ((SELECT @found_perm_id), vid, hid, nnid, workload, (SELECT @found_missing_mode));
        SET perm_id := @found_perm_id;
        SET missing_mode := @found_missing_mode;
    ELSE
        SET perm_id := NULL;
        SET missing_mode := NULL;
    END IF;
END //
DELIMITER ;

CREATE EVENT delete_reserved_permutations
    ON SCHEDULE AT CURRENT_TIMESTAMP + INTERVAL 15 MINUTE
    DO
    DELETE
    FROM dynamic_performance
    WHERE error_id IS NULL
      AND measurement_id IS NULL
      AND TIMESTAMPDIFF(HOUR, last_updated, CURRENT_TIMESTAMP) > 1;

DELIMITER //
CREATE PROCEDURE sp_gr_Error(IN p_edesc TEXT, IN p_etime BIGINT UNSIGNED,
                             IN p_err_type VARCHAR(255), OUT eid BIGINT UNSIGNED)
BEGIN
    INSERT INTO errors (error_desc, time_elapsed_seconds, error_type)
    VALUES (p_edesc, p_etime, p_err_type)
    ON DUPLICATE KEY UPDATE time_elapsed_seconds = p_etime, error_date = DEFAULT;
    SELECT id
    INTO eid
    FROM errors
    WHERE error_desc = p_edesc
      AND error_type = p_err_type;
END //
DELIMITER ;

