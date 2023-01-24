use gvc0;
DROP VIEW IF EXISTS path_step_index;
DROP VIEW IF EXISTS all_errors;
DROP VIEW IF EXISTS completed_benchmarks;
DROP VIEW IF EXISTS completed_paths;
DROP VIEW IF EXISTS completed_programs;
DROP VIEW IF EXISTS static_verification_times;

DROP TABLE IF EXISTS global_configuration;

DROP TABLE IF EXISTS static_performance;
DROP TABLE IF EXISTS static_errors;
DROP TABLE IF EXISTS static_conjuncts;

DROP TABLE IF EXISTS dynamic_performance;
DROP TABLE IF EXISTS dynamic_errors;

DROP TABLE IF EXISTS measurements;
DROP TABLE IF EXISTS static_measurement_types;
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
DROP PROCEDURE IF EXISTS sp_UpdateStaticPerformance;
DROP PROCEDURE IF EXISTS sp_UpdateStaticConjuncts;
DROP PROCEDURE IF EXISTS sp_ReservePermutation;
DROP PROCEDURE IF EXISTS sp_AddMeasurement;
DROP PROCEDURE IF EXISTS sp_AddProgramToBenchmark;
DROP PROCEDURE IF EXISTS sp_ResetBenchmark;
DROP PROCEDURE IF EXISTS sp_UpdateVerifiedPermutation;

DROP TABLE IF EXISTS reserved_jobs;

DROP EVENT IF EXISTS delete_failed_runs;

CREATE TABLE IF NOT EXISTS global_configuration
(
    id              ENUM ('1') DEFAULT '1',
    timeout_minutes BIGINT UNSIGNED NOT NULL,
    timeout_margin  BIGINT UNSIGNED NOT NULL,
    max_paths       BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (id)
);

INSERT INTO global_configuration (timeout_minutes, timeout_margin, max_paths)
VALUES (120, 1, 128);

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
    path_date  DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
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
    benchmark_date DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (id, benchmark_name)
);

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

CREATE TABLE IF NOT EXISTS static_measurement_types
(
    id               SERIAL,
    measurement_type VARCHAR(255) NOT NULL UNIQUE,
    PRIMARY KEY (id)
);

INSERT INTO static_measurement_types (measurement_type)
VALUES ('translation');
INSERT INTO static_measurement_types (measurement_type)
VALUES ('verification');
INSERT INTO static_measurement_types (measurement_type)
VALUES ('instrumentation');
INSERT INTO static_measurement_types (measurement_type)
VALUES ('compilation');

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

CREATE TABLE IF NOT EXISTS static_conjuncts
(
    permutation_id  BIGINT UNSIGNED NOT NULL,
    version_id      BIGINT UNSIGNED NOT NULL,
    conj_total      BIGINT UNSIGNED NOT NULL,
    conj_eliminated BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (permutation_id, version_id),
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id)
);

CREATE TABLE IF NOT EXISTS static_performance
(
    permutation_id             BIGINT UNSIGNED        NOT NULL,
    version_id                 BIGINT UNSIGNED        NOT NULL,
    hardware_id                BIGINT UNSIGNED        NOT NULL,
    nickname_id                BIGINT UNSIGNED        NOT NULL,
    measurement_id             BIGINT UNSIGNED UNIQUE NOT NULL,
    static_measurement_type_id BIGINT UNSIGNED        NOT NULL,
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (nickname_id) REFERENCES nicknames (id)
);

CREATE TABLE IF NOT EXISTS verified_permutations
(
    permutation_id BIGINT UNSIGNED NOT NULL,
    version_id     BIGINT UNSIGNED NOT NULL,
    c0_source      LONGTEXT        NOT NULL,
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    PRIMARY KEY (permutation_id, version_id)
);
DELIMITER //
CREATE PROCEDURE sp_UpdateVerifiedPermutation(IN vid BIGINT UNSIGNED,
                                              IN perm_id BIGINT UNSIGNED, IN c0 LONGTEXT)
BEGIN
    INSERT INTO verified_permutations (permutation_id, version_id, c0_source)
    VALUES (perm_id, vid, c0)
    ON DUPLICATE KEY UPDATE c0_source = c0;
END //
DELIMITER ;


CREATE TABLE IF NOT EXISTS static_errors
(
    permutation_id BIGINT UNSIGNED NOT NULL,
    version_id     BIGINT UNSIGNED NOT NULL,
    hardware_id    BIGINT UNSIGNED NOT NULL,
    nickname_id    BIGINT UNSIGNED NOT NULL,
    error_id       BIGINT UNSIGNED DEFAULT NULL,
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (nickname_id) REFERENCES nicknames (id),
    FOREIGN KEY (error_id) REFERENCES error_occurrences (id)
);

DELIMITER //
CREATE PROCEDURE sp_UpdateStaticPerformance(IN vid BIGINT UNSIGNED, IN hid BIGINT UNSIGNED, IN nid BIGINT UNSIGNED,
                                            IN perm_id BIGINT UNSIGNED, IN m_id BIGINT UNSIGNED,
                                            IN m_type_id BIGINT UNSIGNED)
BEGIN
    INSERT INTO static_performance (permutation_id, version_id, hardware_id, nickname_id, measurement_id,
                                    static_measurement_type_id)
    VALUES (perm_id, vid, hid, nid, m_id, m_type_id)
    ON DUPLICATE KEY UPDATE nickname_id = nid, measurement_id = m_id;
END //
DELIMITER ;

DELIMITER //
CREATE PROCEDURE sp_UpdateStaticConjuncts(IN vid BIGINT UNSIGNED,
                                          IN perm_id BIGINT UNSIGNED, IN n_total BIGINT UNSIGNED,
                                          IN n_elim BIGINT UNSIGNED)
BEGIN
    INSERT INTO static_conjuncts (permutation_id, version_id, conj_total, conj_eliminated)
    VALUES (perm_id, vid, n_total, n_elim)
    ON DUPLICATE KEY UPDATE conj_total = n_total, conj_eliminated = n_elim;
END //
DELIMITER ;


CREATE TABLE IF NOT EXISTS dynamic_performance
(
    permutation_id      BIGINT UNSIGNED NOT NULL,
    measurement_type_id BIGINT UNSIGNED NOT NULL,
    stress              BIGINT UNSIGNED NOT NULL,
    hardware_id         BIGINT UNSIGNED NOT NULL,
    version_id          BIGINT UNSIGNED NOT NULL,
    nickname_id         BIGINT UNSIGNED NOT NULL,
    measurement_id      BIGINT UNSIGNED UNIQUE   DEFAULT NULL,
    last_updated        DATETIME        NOT NULL DEFAULT CURRENT_TIMESTAMP,
    timeout_minutes     BIGINT UNSIGNED NOT NULL,
    PRIMARY KEY (permutation_id, stress, measurement_type_id, hardware_id, version_id, nickname_id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (nickname_id) REFERENCES nicknames (id),
    FOREIGN KEY (measurement_id) REFERENCES measurements (id),
    FOREIGN KEY (measurement_type_id) REFERENCES dynamic_measurement_types (id)
);
CREATE TABLE IF NOT EXISTS dynamic_errors
(
    permutation_id      BIGINT UNSIGNED NOT NULL,
    version_id          BIGINT UNSIGNED NOT NULL,
    hardware_id         BIGINT UNSIGNED NOT NULL,
    nickname_id         BIGINT UNSIGNED NOT NULL,
    stress              BIGINT UNSIGNED NOT NULL,
    measurement_type_id BIGINT UNSIGNED NOT NULL,
    error_id            BIGINT UNSIGNED DEFAULT NULL,
    FOREIGN KEY (permutation_id) REFERENCES permutations (id),
    FOREIGN KEY (version_id) REFERENCES versions (id),
    FOREIGN KEY (hardware_id) REFERENCES hardware (id),
    FOREIGN KEY (nickname_id) REFERENCES nicknames (id),
    FOREIGN KEY (measurement_type_id) REFERENCES dynamic_measurement_types (id),
    FOREIGN KEY (error_id) REFERENCES error_occurrences (id)
);

DELIMITER //
CREATE PROCEDURE sp_ReservePermutation(IN vid BIGINT UNSIGNED, IN hid BIGINT UNSIGNED, IN nnid BIGINT UNSIGNED,
                                       IN exclusive_measurement_type VARCHAR(255),
                                       IN timeout BIGINT UNSIGNED,
                                       IN bonly BOOLEAN,
                                       IN nicknameSensitive BOOLEAN)
BEGIN
    START TRANSACTION;
    DROP TABLE IF EXISTS reserved_jobs;
    CREATE TEMPORARY TABLE reserved_jobs
    (
        permutation_id           BIGINT UNSIGNED        NOT NULL,
        stress                   BIGINT UNSIGNED UNIQUE NOT NULL,
        dynamic_measurement_type BIGINT UNSIGNED        NOT NULL
    );

    SELECT permutations.program_id, permutations.id, dmt.id
    INTO @found_program_id, @found_perm_id, @found_measurement_type_id
    FROM permutations
             CROSS JOIN configured_stress_values sa on permutations.program_id = sa.program_id
             CROSS JOIN dynamic_measurement_types dmt
             CROSS JOIN versions vr
             CROSS JOIN hardware hw
             LEFT OUTER JOIN dynamic_performance dr ON
                dr.measurement_type_id = dmt.id AND
                dr.version_id = vr.id AND
                dr.hardware_id = hw.id AND
                dr.permutation_id = permutations.id AND
                dr.stress = sa.stress AND
                (NOT nicknameSensitive OR dr.nickname_id = nnid)
             LEFT OUTER JOIN dynamic_errors de ON
                dmt.id = de.measurement_type_id AND
                vr.id = de.version_id AND
                hw.id = de.hardware_id AND
                permutations.id = de.permutation_id AND
                (NOT nicknameSensitive OR de.nickname_id = nnid)
             LEFT OUTER JOIN static_errors se ON
                vr.id = se.version_id AND
                hw.id = se.hardware_id AND
                permutations.id = se.permutation_id AND
                (NOT nicknameSensitive OR se.nickname_id = nnid)
    WHERE vr.id = vid
      AND hw.id = hid
      AND (NOT bonly OR permutations.id IN (SELECT permutation_id FROM benchmark_membership))
      AND (ISNULL(exclusive_measurement_type) OR dmt.measurement_type = exclusive_measurement_type)
      AND se.error_id IS NULL
      AND de.error_id IS NULL
      AND dr.permutation_id IS NULL
    ORDER BY RAND()
    LIMIT 1;

    IF ((SELECT @found_perm_id IS NOT NULL) AND (SELECT @found_measurement_type_id IS NOT NULL) AND
        (SELECT @found_program_id IS NOT NULL)) THEN
        INSERT INTO reserved_jobs (SELECT DISTINCT @found_perm_id, sa.stress, @found_measurement_type_id
                                   FROM configured_stress_values sa
                                   WHERE sa.program_id = @found_program_id);
        DELETE
        FROM reserved_jobs
        WHERE stress IN (SELECT stress
                         FROM dynamic_performance dr
                         where dr.measurement_type_id = @found_measurement_type_id
                           AND dr.permutation_id = @found_perm_id
                           AND dr.version_id = vid
                           AND dr.hardware_id = hid
                           AND (NOT nicknameSensitive OR dr.nickname_id = nnid));
        IF ((SELECT COUNT(*) FROM reserved_jobs) < 1) THEN
            SELECT CONCAT('Reservation failed. PID=', @found_perm_id, ' MTID=',
                          @found_measurement_type_id)
            INTO @message_text;
            SIGNAL SQLSTATE '45000'
                SET MESSAGE_TEXT = @message_text;
        END IF;
        INSERT INTO dynamic_performance
        SELECT @found_perm_id,
               @found_measurement_type_id,
               stress,
               hid,
               vid,
               nnid,
               NULL,
               CURRENT_TIMESTAMP,
               timeout
        FROM reserved_jobs;
    END IF;
    COMMIT;
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

CREATE VIEW path_step_index AS
(
SELECT p.program_id,
       p.id       as permutation_id,
       paths.id   as path_id,
       s.level_id as level_id,
       c.context_name,
       c.spec_type,
       c.expr_type
FROM paths
         CROSS JOIN steps s ON paths.id = s.path_id
         CROSS JOIN permutations p on s.permutation_id = p.id
         INNER JOIN components c on s.component_id = c.id
    );

CREATE VIEW all_errors AS
(
SELECT DISTINCT error_subset.version_id,
                error_subset.hardware_id,
                program_id,
                error_subset.permutation_id,
                error_type,
                IF(se.error_id IS NOT NULL AND de.error_id IS NOT NULL,
                   'unknown', IF(de.error_id IS NULL, 'static', 'dynamic')) AS occurred_during,
                measurement_type,
                error_desc,
                error_date
FROM (SELECT DISTINCT version_id, hardware_id, permutation_id, error_id, 'static' AS measurement_type
      FROM static_errors
      UNION ALL
      SELECT DISTINCT version_id, hardware_id, permutation_id, error_id, measurement_type
      FROM dynamic_errors
               INNER JOIN dynamic_measurement_types dmt
                          on dynamic_errors.measurement_type_id = dmt.id) AS error_subset
         INNER JOIN error_occurrences ON error_subset.error_id = error_occurrences.id
         INNER JOIN error_contents ec on error_occurrences.error_contents_id = ec.id
         INNER JOIN permutations p on error_subset.permutation_id = p.id
         LEFT OUTER JOIN static_errors se ON
            error_subset.error_id = se.error_id AND
            error_subset.version_id = se.version_id AND
            error_subset.permutation_id = se.permutation_id AND
            error_subset.hardware_id = se.hardware_id
         LEFT OUTER JOIN dynamic_errors de ON
            error_subset.error_id = de.error_id AND
            error_subset.version_id = de.version_id AND
            error_subset.permutation_id = de.permutation_id AND
            error_subset.hardware_id = de.hardware_id AND
            error_subset.measurement_type =
            (SELECT measurement_type FROM dynamic_measurement_types WHERE id = de.measurement_type_id)
    );

CREATE VIEW completed_paths AS
(
SELECT paths.program_id, path_id, version_id, hardware_id, stress, measurement_type_id
FROM (SELECT path_id,
             version_id,
             hardware_id,
             stress,
             measurement_type_id,
             COUNT(DISTINCT dp.permutation_id) AS completed
      FROM dynamic_performance dp
               CROSS JOIN steps ON steps.permutation_id = dp.permutation_id
               INNER JOIN paths p on steps.path_id = p.id
      WHERE dp.measurement_id IS NOT NULL
      GROUP BY path_id, version_id, hardware_id, stress, measurement_type_id) counts
         INNER JOIN paths ON counts.path_id = paths.id
         INNER JOIN (SELECT program_id, COUNT(*) AS maximum FROM components GROUP BY(program_id))
    AS max_counts ON paths.program_id = max_counts.program_id
WHERE counts.completed = (max_counts.maximum + 1));

CREATE VIEW completed_benchmarks AS
(
SELECT counts.benchmark_id, version_id, hardware_id, stress, measurement_type_id
FROM (SELECT benchmark_id,
             version_id,
             hardware_id,
             stress,
             measurement_type_id,
             COUNT(DISTINCT dp.permutation_id) AS completed
      FROM dynamic_performance dp
               CROSS JOIN benchmark_membership bm on dp.permutation_id = bm.permutation_id
      WHERE dp.measurement_id IS NOT NULL
      GROUP BY benchmark_id, version_id, hardware_id, stress, measurement_type_id) as counts
         INNER JOIN (SELECT benchmark_id, COUNT(*) AS maximum FROM benchmark_membership GROUP BY(benchmark_id))
    AS max_counts ON counts.benchmark_id = max_counts.benchmark_id
WHERE counts.completed = max_counts.maximum);
CREATE VIEW completed_programs AS
(
SELECT A.program_id,
       A.version_id,
       A.hardware_id,
       A.stress,
       A.measurement_type_id,
       completed,
       IFNULL(stat_errored, 0) AS static_errored,
       IFNULL(dyn_errored, 0)  AS dynamic_errored,
       total
FROM (SELECT program_id,
             version_id,
             hardware_id,
             stress,
             measurement_type_id,
             COUNT(DISTINCT dp.permutation_id) AS completed
      FROM dynamic_performance dp
               INNER JOIN permutations p2 on dp.permutation_id = p2.id
      WHERE dp.measurement_id IS NOT NULL
      GROUP BY program_id, version_id, hardware_id, stress, measurement_type_id) AS A
         LEFT OUTER JOIN
     (SELECT program_id,
             version_id,
             hardware_id,
             stress,
             measurement_type_id,
             COUNT(DISTINCT dp.permutation_id) AS dyn_errored
      FROM dynamic_errors dp
               INNER JOIN permutations p2 on dp.permutation_id = p2.id
      GROUP BY program_id, version_id, hardware_id, stress, measurement_type_id) AS B
     ON A.program_id = B.program_id AND A.stress = B.stress AND A.hardware_id = B.hardware_id AND
        A.measurement_type_id = B.measurement_type_id AND
        A.version_id = B.version_id
         LEFT OUTER JOIN
     (SELECT program_id,
             version_id,
             hardware_id,
             COUNT(DISTINCT dp.permutation_id) AS stat_errored
      FROM static_errors dp
               INNER JOIN permutations p2 on dp.permutation_id = p2.id
      GROUP BY program_id, version_id, hardware_id) AS C
     ON A.program_id = C.program_id AND A.hardware_id = C.hardware_id AND
        A.version_id = C.version_id
         INNER JOIN (SELECT program_id, COUNT(*) AS total FROM permutations GROUP BY program_id) AS D
                    ON A.program_id = D.program_id
    );

DELIMITER //
CREATE PROCEDURE sp_ResetBenchmark(IN p_bench_name VARCHAR(255), IN p_bench_desc TEXT)
BEGIN
    SELECT id INTO @original_id FROM benchmarks WHERE benchmark_name = p_bench_name;
    IF (SELECT @original_id IS NOT NULL) THEN
        DELETE FROM benchmark_membership WHERE benchmark_id = @original_id;
        DELETE FROM benchmarks WHERE id = @original_id;
    END IF;
    INSERT INTO benchmarks (benchmark_name, benchmark_desc) VALUES (p_bench_name, p_bench_desc);
    SELECT LAST_INSERT_ID() INTO @found_id;
    SELECT @found_id;
END //
DELIMITER ;

DELIMITER //
CREATE PROCEDURE sp_AddProgramToBenchmark(IN p_perm_id BIGINT UNSIGNED, IN p_benchmark_id BIGINT UNSIGNED)
BEGIN
    INSERT INTO benchmark_membership (benchmark_id, permutation_id) VALUES (p_benchmark_id, p_perm_id);
END //
DELIMITER ;

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

CREATE EVENT delete_failed_runs ON SCHEDULE EVERY 3 HOUR ENABLE
    DO
    DELETE
    FROM dynamic_performance
    WHERE TIMESTAMPDIFF(MINUTE, last_updated, CURRENT_TIMESTAMP) >
          dynamic_performance.timeout_minutes + (0.5 * dynamic_performance.timeout_minutes)
      AND measurement_id IS NULL;

CREATE VIEW static_verification_times AS
SELECT program_id, version_id, hardware_id, MAX(elapsed) as max, AVG(elapsed) as mean
FROM (SELECT p3.program_id, version_id, hardware_id, FLOOR((median / POW(10, 9)) / 60) AS elapsed
      FROM static_performance sp
               INNER JOIN static_measurement_types smt ON sp.static_measurement_type_id = smt.id
               INNER JOIN measurements m on sp.measurement_id = m.id
               INNER JOIN permutations p3 on sp.permutation_id = p3.id
      WHERE permutation_id IN (select distinct permutation_id
                               from dynamic_performance dp
                                        INNER JOIN permutations p ON dp.permutation_id = p.id
                                        INNER JOIN programs p2 on p.program_id = p2.id
                                        INNER JOIN dynamic_measurement_types dmt on dp.measurement_type_id = dmt.id
                               WHERE dmt.measurement_type = 'gradual')
        AND measurement_type = 'verification'
      ORDER BY elapsed DESC) as et
GROUP BY program_id, version_id, hardware_id;