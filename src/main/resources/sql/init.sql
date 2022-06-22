CREATE TABLE IF NOT EXISTS programs (
    id SERIAL,
    hash UUID NOT NULL,
    src TEXT NOT NULL,
    PRIMARY KEY (id)
)
CREATE TABLE IF NOT EXISTS permutations (
     id SERIAL,
     program_id SERIAL NOT NULL,
     path_id SERIAL NOT NULL,
     level_id SERIAL NOT NULL,
     component_added VARCHAR(511) NOT NULL,
     PRIMARY KEY (id),
     FOREIGN KEY (program_id) REFERENCES programs(id)
)
CREATE TABLE IF NOT EXISTS versions (
      id SERIAL,
      version_name VARCHAR(255) NOT NULL,
      PRIMARY KEY (id)
)
CREATE TABLE IF NOT EXISTS hardware (
      id SERIAL,
      description VARCHAR(255) NOT NULL,
      PRIMARY KEY (id)
)
CREATE TABLE IF NOT EXISTS conjuncts (
      id SERIAL,
      perm_id SERIAL,
      version_id SERIAL,
      conj_total SERIAL NOT NULL,
      conj_eliminated NOT NULL,
      PRIMARY KEY (id),
      FOREIGN KEY (perm_id) REFERENCES permutations(id),
      FOREIGN KEY (version_id) REFERENCES versions(id)
)

CREATE TABLE IF NOT EXISTS performance (
    id SERIAL,
    program_id SERIAL,
    version_id SERIAL,
    hw_id SERIAL,
    mode VARCHAR(255) NOT NULL,
    stress INTEGER,
    iter INTEGER NOT NULL,
    95th DOUBLE PRECISION NOT NULL,
    5th DOUBLE PRECISION NOT NULL,
    median DOUBLE PRECISION NOT NULL,
    mean DOUBLE PRECISION NOT NULL,
    stdev DOUBLE PRECISION NOT NULL,
    minimum DOUBLE PRECISION NOT NULL,
    maximum DOUBLE PRECISION NOT NULL,
    FOREIGN KEY (program_id) REFERENCES programs(id),
    FOREIGN KEY (hw_id) REFERENCES hardware(id),
    FOREIGN KEY (version_id) REFERENCES versions(id),
)