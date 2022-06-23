CREATE TABLE IF NOT EXISTS programs (
    id SERIAL,
    hash UUID NOT NULL,
    src TEXT NOT NULL,
    program_date DATE NOT NULL DEFAULT CURRENT_DATE,
    PRIMARY KEY (id) 
)
CREATE TABLE IF NOT EXISTS components (
    id SERIAL,
    fn_name VARCHAR(255) NOT NULL, 
    spec_id SERIAL NOT NULL, 
    spec_type VARCHAR(255) NOT NULL, 
    expr_type VARCHAR(255) NOT NULL, 
    spec_index SERIAL NOT NULL, 
    expr_index SERIAL NOT NULL,
    component_date DATE NOT NULL DEFAULT CURRENT_DATE,
    PRIMARY KEY (id)
)
CREATE TABLE IF NOT EXISTS permutations (
     id SERIAL,
     program_id SERIAL NOT NULL,
     path_id SERIAL NOT NULL,
     level_id SERIAL NOT NULL,
     component_id SERIAL NOT NULL,
     permutation_date DATE NOT NULL DEFAULT CURRENT_DATE,
     PRIMARY KEY (id),
     FOREIGN KEY (component_id) REFERENCES components(id),
     FOREIGN KEY (program_id) REFERENCES programs(id)
)
CREATE TABLE IF NOT EXISTS versions (
      id SERIAL,
      version_name VARCHAR(255) NOT NULL,
      version_date DATE NOT NULL DEFAULT CURRENT_DATE,
      PRIMARY KEY (id) 
)
CREATE TABLE IF NOT EXISTS hardware (
      id SERIAL,
      description VARCHAR(255) NOT NULL,
      hardware_date DATE NOT NULL DEFAULT CURRENT_DATE,
      PRIMARY KEY (id) 
)
CREATE TABLE IF NOT EXISTS conjuncts (
      id SERIAL,
      perm_id SERIAL,
      version_id SERIAL,
      conj_total SERIAL NOT NULL,
      conj_eliminated NOT NULL,
      conj_date DATE NOT NULL DEFAULT CURRENT_DATE,
      PRIMARY KEY (id),
      FOREIGN KEY (perm_id) REFERENCES permutations(id),
      FOREIGN KEY (version_id) REFERENCES versions(id) 
)

CREATE TABLE IF NOT EXISTS performance (
    id SERIAL,
    program_id SERIAL,
    version_id SERIAL,
    hw_id SERIAL,
    performance_date DATE NOT NULL DEFAULT CURRENT_DATE,
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
    FOREIGN KEY (version_id) REFERENCES versions(id) 
)