int c_rips_dm(int** n_intervals, value_t** births_and_deaths,
              int** cocycle_length, int** cocycles,
              value_t* D, int N, int modulus, int dim_max, value_t threshold);

int c_rips_dm_sparse(int** n_intervals, value_t** births_and_deaths,
                     int** cocycle_length, int** cocycles,
                     int* I, int* J, float* V, int NEdges, int N,
                     int modulus, int dim_max, float threshold);

int c_rips_dm_cycles(int** n_intervals, value_t** births_and_deaths,
              int** cycle_length, int** cycles,
              value_t* D, int N, int modulus, int dim_max, value_t threshold);

int c_rips_dm_sparse_cycles(int** n_intervals, value_t** births_and_deaths,
                     int** cycle_length, int** cycles,
                     int* I, int* J, float* V, int NEdges, int N,
                     int modulus, int dim_max, float threshold);
