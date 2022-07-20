DROP DATABASE IF EXISTS gvc0;
CREATE DATABASE gvc0;
USE gvc0;

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
    PRIMARY KEY (id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Program(IN p_name VARCHAR(255), IN p_hash VARCHAR(255), IN p_labels BIGINT UNSIGNED,
                               OUT p_id BIGINT UNSIGNED)
BEGIN
    SELECT id INTO p_id FROM programs WHERE src_filename = p_name AND src_hash = p_hash AND num_labels = p_labels;

    IF ((SELECT p_id) IS NULL) THEN
        INSERT INTO programs (src_filename, src_hash, num_labels) VALUES (p_name, p_hash, p_labels);
        SELECT LAST_INSERT_ID() INTO p_id;
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
                                 IN p_eindex BIGINT UNSIGNED,
                                 OUT c_id BIGINT UNSIGNED)
BEGIN
    SELECT id
    INTO c_id
    FROM components
    WHERE program_id = p_id
      AND context_name = p_cname
      AND spec_type = p_stype
      AND spec_index = p_sindex
      AND expr_type = p_etype
      AND expr_index = p_eindex;
    IF ((SELECT c_id) IS NULL) THEN
        INSERT INTO components (program_id, context_name, spec_type, spec_index, expr_type, expr_index)
        VALUES (p_id, p_cname, p_stype, p_sindex, p_etype, p_eindex);
        SELECT LAST_INSERT_ID() INTO c_id;
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
CREATE PROCEDURE sp_gr_Permutation(IN p_program_id BIGINT UNSIGNED, IN p_perm_hash TEXT, OUT p_id BIGINT UNSIGNED)
BEGIN
    SELECT id INTO p_id FROM permutations WHERE program_id = p_program_id AND permutation_hash = p_perm_hash;
    IF ((SELECT p_id) IS NULL) THEN
        INSERT INTO permutations (program_id, permutation_hash) VALUES (p_program_id, p_perm_hash);
        SELECT LAST_INSERT_ID() INTO p_id;
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
    PRIMARY KEY (id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Version(IN p_name VARCHAR(255), OUT v_id BIGINT UNSIGNED)
BEGIN
    SELECT id INTO v_id FROM versions WHERE version_name = p_name;
    IF ((SELECT v_id) IS NULL) THEN
        INSERT INTO versions (version_name) VALUES (p_name);
        SELECT LAST_INSERT_ID() INTO v_id;
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
CREATE PROCEDURE sp_gr_Hardware(IN p_name VARCHAR(255), OUT h_id BIGINT UNSIGNED)
BEGIN
    SELECT id INTO h_id FROM hardware WHERE hardware_name = p_name;
    IF ((SELECT h_id) IS NULL) THEN
        INSERT INTO hardware (hardware_name) VALUES (p_name);
        SELECT LAST_INSERT_ID() INTO h_id;
    END IF;
END //
DELIMITER ;

CREATE TABLE IF NOT EXISTS compilation_metadata
(
    id                        SERIAL,
    permutation_id            BIGINT UNSIGNED NOT NULL,
    version_id                BIGINT UNSIGNED NOT NULL,
    hardware_id               BIGINT UNSIGNED NOT NULL,
    conj_total                BIGINT UNSIGNED NOT NULL,
    conj_eliminated           BIGINT UNSIGNED NOT NULL,
    conj_date                 DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    verification_time_secs    BIGINT UNSIGNED NOT NULL,
    translation_time_secs     BIGINT UNSIGNED NOT NULL,
    instrumentation_time_secs BIGINT UNSIGNED NOT NULL,
    compilation_time_secs     BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (id),
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id)
);

CREATE TABLE IF NOT EXISTS benchmarks
(
    id             SERIAL,
    benchmark_name VARCHAR(255),
    benchmark_desc TEXT,
    PRIMARY KEY (id)
);

CREATE TABLE IF NOT EXISTS benchmark_membership
(
    benchmark_id   BIGINT UNSIGNED NOT NULL,
    permutation_id BIGINT UNSIGNED NOT NULL,
    FOREIGN KEY (benchmark_id) REFERENCES benchmarks (id),
    FOREIGN KEY (permutation_id) REFERENCES permutations (id)
);

CREATE TABLE IF NOT EXISTS dynamic_measurement_types
(
    id   SERIAL,
    type VARCHAR(255) NOT NULL UNIQUE,
    PRIMARY KEY (id)
);

INSERT INTO dynamic_measurement_types (type)
VALUES ('gradual');
INSERT INTO dynamic_measurement_types (type)
VALUES ('framing');
INSERT INTO dynamic_measurement_types (type)
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
    error_desc           TEXT,
    error_date           DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
    error_type           ENUM ('verification', 'compilation', 'execution'),
    time_elapsed_seconds BIGINT UNSIGNED,
    PRIMARY KEY (id)
);



CREATE TABLE IF NOT EXISTS static_performance
(
    permutation_id          BIGINT UNSIGNED NOT NULL,
    version_id              BIGINT UNSIGNED NOT NULL,
    hardware_id             BIGINT UNSIGNED NOT NULL,
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
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (error_id) REFERENCES errors (id),
    PRIMARY KEY (permutation_id, version_id, hardware_id)
);

DELIMITER //
CREATE PROCEDURE sp_UpdateStatic(IN vid BIGINT UNSIGNED, IN hid BIGINT UNSIGNED,
                                 IN perm_id BIGINT UNSIGNED, IN tr_id BIGINT UNSIGNED, IN vf_id BIGINT UNSIGNED,
                                 IN inst_id BIGINT UNSIGNED, IN cp_id BIGINT UNSIGNED, IN total_cond BIGINT UNSIGNED,
                                 IN elim_cond BIGINT UNSIGNED, IN err_id BIGINT UNSIGNED)
BEGIN
    SELECT @ex = version_id,
           @ex_tr = translation_perf_id,
           @ex_vf = verification_perf_id,
           @ex_inst = instrumentation_perf_id,
           @ex_cp = compilation_perf_id
    FROM static_performance
    WHERE version_id = vid
      AND hardware_id = hid
      AND permutation_id = perm_id;
    IF ((SELECT @ex) IS NOT NULL) THEN
        UPDATE static_performance
        SET translation_perf_id     = tr_id,
            verification_perf_id    = vf_id,
            instrumentation_perf_id = inst_id,
            compilation_perf_id     = cp_id,
            conj_total              = total_cond,
            conj_eliminated         = elim_cond,
            error_id                = err_id
        WHERE version_id = vid
          AND hardware_id = hid
          AND permutation_id = perm_id;
        DELETE FROM measurements WHERE id = (SELECT @ex_tr);
        DELETE FROM measurements WHERE id = (SELECT @ex_vf);
        DELETE FROM measurements WHERE id = (SELECT @ex_inst);
        DELETE FROM measurements WHERE id = (SELECT @ex_cp);
    ELSE
        INSERT INTO static_performance (permutation_id, version_id, hardware_id, translation_perf_id,
                                        verification_perf_id, instrumentation_perf_id, compilation_perf_id, conj_total,
                                        conj_eliminated, error_id)
        VALUES (perm_id, vid, hid, tr_id, vf_id, inst_id, cp_id, total_cond, elim_cond, err_id);
    END IF;
end //
DELIMITER ;

CREATE TABLE IF NOT EXISTS dynamic_performance
(
    id                       SERIAL,
    permutation_id           BIGINT UNSIGNED NOT NULL,
    version_id               BIGINT UNSIGNED NOT NULL,
    hardware_id              BIGINT UNSIGNED NOT NULL,
    stress                   INTEGER         NOT NULL,
    dynamic_measurement_type BIGINT UNSIGNED NOT NULL,
    measurement_id           BIGINT UNSIGNED          DEFAULT NULL,
    last_updated             DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    error_id                 BIGINT UNSIGNED          DEFAULT NULL,
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (dynamic_measurement_type) REFERENCES dynamic_measurement_types (id),
    FOREIGN KEY (measurement_id) REFERENCES measurements (id),
    FOREIGN KEY (error_id) REFERENCES errors (id),
    PRIMARY KEY (id)
);

DROP PROCEDURE sp_ReservePermutation;
DELIMITER //
CREATE PROCEDURE sp_ReservePermutation(IN vid BIGINT UNSIGNED, IN hid BIGINT UNSIGNED, IN workload BIGINT UNSIGNED,
                                       OUT perm_id BIGINT UNSIGNED, OUT perf_id BIGINT UNSIGNED,
                                       OUT missing_mode VARCHAR(255))
BEGIN
    SELECT id
    INTO perm_id
    FROM permutations
             LEFT OUTER JOIN (SELECT permutation_id
                              FROM dynamic_performance
                              WHERE version_id = vid
                                AND hardware_id = hid
                                AND stress = workload) as `p*`
                             ON permutations.id = `p*`.permutation_id
    WHERE `p*`.permutation_id IS NULL
    LIMIT 1;

    IF ((SELECT perm_id) IS NOT NULL) THEN
        SELECT id
        INTO @missing_mode_id
        FROM dynamic_measurement_types
        WHERE id NOT IN (SELECT dynamic_measurement_type
                         FROM dynamic_performance
                         WHERE permutation_id = (SELECT perm_id))
        LIMIT 1;

        INSERT INTO dynamic_performance (permutation_id, version_id, hardware_id, stress, dynamic_measurement_type)
        VALUES ((SELECT perm_id), vid, hid, workload, @missing_mode_id);
        SELECT LAST_INSERT_ID() INTO perf_id;
        SELECT type INTO missing_mode FROM dynamic_measurement_types WHERE id = (SELECT @missing_mode_id);
    ELSE
        SELECT NULL INTO missing_mode;
        SELECT NULL INTO perf_id;
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
                             IN type ENUM ('verification', 'compilation', 'execution'), OUT eid BIGINT UNSIGNED)
BEGIN
    SELECT id
    INTO eid
    FROM errors
    WHERE error_desc = p_edesc
      AND error_type = type;
    IF ((SELECT eid) IS NULL) THEN
        INSERT INTO errors (error_desc, time_elapsed_seconds, error_type)
        VALUES (p_edesc, p_etime, type);
        SELECT LAST_INSERT_ID() INTO eid;
    ELSE
        UPDATE errors SET time_elapsed_seconds = p_etime, error_date = DEFAULT WHERE id = (SELECT eid);
    END IF;
END;