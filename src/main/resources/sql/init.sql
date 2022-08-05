DROP TABLE IF EXISTS global_configuration;
DROP TABLE IF EXISTS static_performance;
DROP TABLE IF EXISTS results;
DROP TABLE IF EXISTS dynamic_performance;
DROP TABLE IF EXISTS measurements;
DROP TABLE IF EXISTS dynamic_measurement_types;
DROP TABLE IF EXISTS error_occurrences;
DROP TABLE IF EXISTS error_contents;
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
DROP PROCEDURE IF EXISTS sp_gr_Permutation;
DROP PROCEDURE IF EXISTS sp_gr_Component;
DROP PROCEDURE IF EXISTS sp_gr_Error;
DROP PROCEDURE IF EXISTS sp_gr_Hardware;
DROP PROCEDURE IF EXISTS sp_gr_Version;
DROP PROCEDURE IF EXISTS sp_gr_Nickname;
DROP PROCEDURE IF EXISTS sp_gr_Program;
DROP PROCEDURE IF EXISTS sp_gr_Path;

DROP PROCEDURE IF EXISTS sp_UpdateStatic;
DROP PROCEDURE IF EXISTS sp_ReservePermutation;
DROP PROCEDURE IF EXISTS sp_AddMeasurement;

DROP EVENT IF EXISTS delete_reserved_permutations;

CREATE TABLE IF NOT EXISTS global_configuration
(
    id              ENUM ('1') DEFAULT '1',
    timeout_minutes BIGINT UNSIGNED NOT NULL,
    timeout_margin  BIGINT UNSIGNED NOT NULL,
    max_paths       BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (id)
);

INSERT INTO global_configuration (timeout_minutes, timeout_margin, max_paths)
VALUES (45, 1, 128);

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
CREATE PROCEDURE sp_gr_Program(IN p_name VARCHAR(255), IN p_hash VARCHAR(255), IN p_labels BIGINT UNSIGNED)
BEGIN
    INSERT IGNORE INTO programs (src_filename, src_hash, num_labels) VALUES (p_name, p_hash, p_labels);
    SELECT id
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
                                 IN p_eindex BIGINT UNSIGNED)
BEGIN
    INSERT IGNORE INTO components (program_id, context_name, spec_type, spec_index, expr_type, expr_index)
    VALUES (p_id, p_cname, p_stype, p_sindex, p_etype, p_eindex);
    SELECT id
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
    id                   SERIAL,
    program_id           BIGINT UNSIGNED NOT NULL,
    permutation_hash     VARCHAR(255)    NOT NULL,
    permutation_contents BLOB            NOT NULL,
    permutation_date     DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id),
    FOREIGN KEY (program_id) REFERENCES programs (id),
    UNIQUE KEY (permutation_hash, program_id)
);

DELIMITER //
CREATE PROCEDURE sp_gr_Permutation(IN p_program_id BIGINT UNSIGNED, IN p_perm_hash VARCHAR(255),
                                   IN p_perm_contents BLOB)
BEGIN
    INSERT IGNORE INTO permutations (program_id, permutation_hash, permutation_contents)
    VALUES (p_program_id, p_perm_hash, p_perm_contents);
    SELECT id FROM permutations WHERE program_id = p_program_id AND permutation_hash = p_perm_hash;
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

DELIMITER //
CREATE PROCEDURE sp_gr_Path(IN p_program_id BIGINT UNSIGNED, IN p_path_hash BLOB)
BEGIN
    INSERT IGNORE INTO paths (program_id, path_hash) VALUES (p_program_id, p_path_hash);
    SELECT id FROM paths WHERE program_id = p_program_id AND path_hash = p_path_hash;
END //
DELIMITER ;


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
CREATE PROCEDURE sp_gr_Version(IN p_name VARCHAR(255))
BEGIN
    INSERT IGNORE INTO versions (version_name) VALUES (p_name);
    SELECT id FROM versions WHERE version_name = p_name;
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
CREATE PROCEDURE sp_gr_Hardware(IN p_name VARCHAR(255))
BEGIN
    INSERT IGNORE INTO hardware (hardware_name) VALUES (p_name);
    SELECT id FROM hardware WHERE hardware_name = p_name;
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
CREATE PROCEDURE sp_gr_Nickname(IN p_nname VARCHAR(255))
BEGIN
    INSERT IGNORE INTO nicknames (nickname) VALUES (p_nname);
    SELECT id FROM nicknames WHERE nickname = p_nname;
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

CREATE TABLE IF NOT EXISTS error_occurrences
(
    id                SERIAL,
    error_contents_id BIGINT UNSIGNED NOT NULL,
    error_type        VARCHAR(255)    NOT NULL,
    error_date        DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id)
);

CREATE TABLE IF NOT EXISTS error_contents
(
    id         SERIAL,
    error_hash VARCHAR(255) UNIQUE NOT NULL,
    error_desc TEXT DEFAULT NULL,
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
    FOREIGN KEY (error_id) REFERENCES error_occurrences (id),
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
        SHARE;
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
    id                       SERIAL,
    permutation_id           BIGINT UNSIGNED NOT NULL,
    stress                   INTEGER         NOT NULL,
    dynamic_measurement_type BIGINT UNSIGNED NOT NULL,
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (dynamic_measurement_type) REFERENCES dynamic_measurement_types (id),
    PRIMARY KEY (permutation_id, stress, dynamic_measurement_type)
);

CREATE TABLE IF NOT EXISTS results
(
    stress_config_id BIGINT UNSIGNED NOT NULL,
    hardware_id      BIGINT UNSIGNED NOT NULL,
    version_id       BIGINT UNSIGNED NOT NULL,
    nickname_id      BIGINT UNSIGNED NOT NULL,
    measurement_id   BIGINT UNSIGNED          DEFAULT NULL,
    error_id         BIGINT UNSIGNED          DEFAULT NULL,
    last_updated     DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (stress_config_id, hardware_id, version_id, nickname_id),
    FOREIGN KEY (stress_config_id) REFERENCES dynamic_performance (id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (nickname_id) REFERENCES nicknames (id),
    FOREIGN KEY (measurement_id) REFERENCES measurements (id)
);
DELIMITER //
CREATE PROCEDURE sp_ReservePermutation(IN vid BIGINT UNSIGNED, IN hid BIGINT UNSIGNED, IN nnid BIGINT UNSIGNED)
BEGIN
    DECLARE c_reserved BIGINT UNSIGNED;
    DECLARE done INT DEFAULT FALSE;
    DECLARE cursor_reserved CURSOR FOR SELECT id FROM reserved_jobs ORDER BY reserved_jobs.stress;
    DECLARE CONTINUE HANDLER FOR NOT FOUND SET done = TRUE;
    DROP TABLE IF EXISTS reserved_jobs;
    CREATE TEMPORARY TABLE reserved_jobs
    (
        id                       BIGINT UNSIGNED UNIQUE NOT NULL,
        permutation_id           BIGINT UNSIGNED        NOT NULL,
        stress                   BIGINT UNSIGNED UNIQUE NOT NULL,
        dynamic_measurement_type BIGINT UNSIGNED        NOT NULL
    );
    SELECT DISTINCT permutation_id, dynamic_measurement_type
    INTO @found_perm_id, @found_type_id
    FROM dynamic_performance
             LEFT OUTER JOIN results ON dynamic_performance.id = results.stress_config_id
        AND results.version_id = vid
        AND results.nickname_id = nnid
        AND results.hardware_id = hid
    WHERE results.stress_config_id IS NULL
    LIMIT 1
    FOR
    UPDATE OF dynamic_performance SKIP LOCKED;

    INSERT INTO reserved_jobs (SELECT *
                               FROM dynamic_performance
                               where dynamic_performance.permutation_id = @found_perm_id
                                 AND dynamic_performance.dynamic_measurement_type = @found_type_id);
    IF ((SELECT COUNT(*) FROM reserved_jobs) > 0) THEN
        OPEN cursor_reserved;
        SET @counter := 0;
        loop_through_rows:
        LOOP
            FETCH cursor_reserved INTO c_reserved;
            IF done THEN
                LEAVE loop_through_rows;
            ELSE
                INSERT INTO results (stress_config_id, hardware_id, version_id, nickname_id)
                VALUES (c_reserved, hid, vid, nnid);
                SET @counter := @counter + 1;
            END IF;
        END LOOP;
        CLOSE cursor_reserved;
    END IF;
    SELECT * FROM reserved_jobs;
END //
DELIMITER ;

DELIMITER //
CREATE PROCEDURE sp_gr_Error(IN p_ehash VARCHAR(255), IN p_edesc TEXT,
                             IN p_err_type VARCHAR(255))
BEGIN
    INSERT IGNORE INTO error_contents (error_hash, error_desc) VALUES (p_ehash, p_edesc);
    SELECT id INTO @found_error_contents FROM error_contents WHERE error_hash = p_ehash AND error_desc = p_edesc;
    INSERT INTO error_occurrences (error_contents_id, error_type)
    VALUES ((SELECT @found_error_contents), p_err_type);
    SELECT LAST_INSERT_ID();
END //
DELIMITER ;

DELIMITER //
CREATE PROCEDURE sp_AddMeasurement(IN p_iterations INT UNSIGNED, IN p_ninety_fifth DOUBLE PRECISION,
                                   IN p_fifth DOUBLE PRECISION, IN p_median DOUBLE PRECISION,
                                   IN p_mean DOUBLE PRECISION,
                                   IN p_stdev DOUBLE PRECISION, IN p_max DOUBLE PRECISION, IN p_min DOUBLE PRECISION)
BEGIN
    INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum)
    VALUES (p_iterations, p_ninety_fifth, p_fifth, p_median, p_mean, p_stdev, p_max, p_min);
    SELECT LAST_INSERT_ID();
END //
DELIMITER ;