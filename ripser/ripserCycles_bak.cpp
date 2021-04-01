/*

 Ripser: a lean C++ code for computation of Vietoris-Rips persistence barcodes

 MIT License

 Copyright (c) 2015–2019 Ulrich Bauer

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.

 You are under no obligation whatsoever to provide any bug fixes, patches, or
 upgrades to the features, functionality or performance of the source code
 ("Enhancements") to anyone; however, if you choose to make your Enhancements
 available either publicly, or directly to the author of this software, without
 imposing a separate written license agreement for such Enhancements, then you
 hereby grant the following license: a non-exclusive, royalty-free perpetual
 license to install, use, modify, prepare derivative works, incorporate into
 other computer software, distribute, and sublicense such enhancements or
 derivative works thereof, in binary and source code form.

*/

//#define USE_COEFFICIENTS

#define INDICATE_PROGRESS
#define PRINT_PERSISTENCE_PAIRS

//#define USE_ROBINHOOD_HASHMAP

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <numeric>
#include <queue>
#include <sstream>
#include <unordered_map>

#ifdef USE_ROBINHOOD_HASHMAP

#include <robin_hood.h>

template <class Key, class T, class H, class E>
using cyc_hash_map = robin_hood::unordered_map<Key, T, H, E>;
template <class Key> using cyc_hash = robin_hood::hash<Key>;

#else

template <class Key, class T, class H, class E> using cyc_hash_map = std::unordered_map<Key, T, H, E>;
template <class Key> using cyc_hash = std::hash<Key>;

#endif

typedef float cyc_value_t;
typedef int64_t cyc_index_t;
typedef uint16_t cyc_coefficient_t;

#ifdef INDICATE_PROGRESS
static const std::chrono::milliseconds time_step(40);
#endif

static const std::string cyc_clear_line("\r\033[K");

static const size_t cyc_num_coefficient_bits = 8;

static const cyc_index_t cyc_max_simplex_index =
    (1l << (8 * sizeof(cyc_index_t) - 1 - cyc_num_coefficient_bits)) - 1;

void cyc_check_overflow(cyc_index_t i) {
	if
#ifdef USE_COEFFICIENTS
	    (i > cyc_max_simplex_index)
#else
	    (i < 0)
#endif
		throw std::overflow_error("simplex index " + std::to_string((uint64_t)i) +
		                          " in filtration is larger than maximum index " +
		                          std::to_string(cyc_max_simplex_index));
}

class cyc_binomial_coeff_table {
	std::vector<std::vector<cyc_index_t>> B;

public:
	cyc_binomial_coeff_table(cyc_index_t n, cyc_index_t k) : B(n + 1) {
		for (cyc_index_t i = 0; i <= n; ++i) {
			B[i].resize(k + 1, 0);
			B[i][0] = 1;
			for (cyc_index_t j = 1; j < std::min(i, k + 1); ++j)
				B[i][j] = B[i - 1][j - 1] + B[i - 1][j];
			if (i <= k) B[i][i] = 1;
			cyc_check_overflow(B[i][std::min(i >> 1, k)]);
		}
	}

	cyc_index_t operator()(cyc_index_t n, cyc_index_t k) const {
		assert(n < B.size() && k < B[n].size() && n >= k - 1);
		return B[n][k];
	}
};

bool is_prime(const cyc_coefficient_t n) {
	if (!(n & 1) || n < 2) return n == 2;
	for (cyc_coefficient_t p = 3; p <= n / p; p += 2)
		if (!(n % p)) return false;
	return true;
}

cyc_coefficient_t cyc_normalize(const cyc_coefficient_t n, const cyc_coefficient_t modulus) {
	return n > modulus / 2 ? n - modulus : n;
}

std::vector<cyc_coefficient_t> cyc_multiplicative_inverse_vector(const cyc_coefficient_t m) {
	std::vector<cyc_coefficient_t> inverse(m);
	inverse[1] = 1;
	// m = a * (m / a) + m % a
	// Multipying with inverse(a) * inverse(m % a):
	// 0 = inverse(m % a) * (m / a) + inverse(a)  (mod m)
	for (cyc_coefficient_t a = 2; a < m; ++a) inverse[a] = m - (inverse[m % a] * (m / a)) % m;
	return inverse;
}

#ifdef USE_COEFFICIENTS

struct __attribute__((packed)) cyc_entry_t {
	cyc_index_t index : 8 * sizeof(cyc_index_t) - cyc_num_coefficient_bits;
	cyc_coefficient_t coefficient : cyc_num_coefficient_bits;
	cyc_entry_t(cyc_index_t _index, cyc_coefficient_t _coefficient)
	    : index(_index), coefficient(_coefficient) {}
	cyc_entry_t(cyc_index_t _index) : index(_index), coefficient(0) {}
	cyc_entry_t() : index(0), coefficient(0) {}	
};

static_assert(sizeof(cyc_entry_t) == sizeof(cyc_index_t), "size of cyc_entry_t is not the same as cyc_index_t");

cyc_entry_t cyc_make_entry(cyc_index_t i, cyc_coefficient_t c) { return cyc_entry_t(i, c); }
cyc_index_t cyc_get_index(const cyc_entry_t& e) { return e.index; }
cyc_index_t cyc_get_coefficient(const cyc_entry_t& e) { return e.coefficient; }
void cyc_set_coefficient(cyc_entry_t& e, const cyc_coefficient_t c) { e.coefficient = c; }

std::ostream& operator<<(std::ostream& stream, const cyc_entry_t& e) {
	stream << cyc_get_index(e) << ":" << cyc_get_coefficient(e);
	return stream;
}

#else

typedef cyc_index_t cyc_entry_t;
const cyc_index_t cyc_get_index(const cyc_entry_t& i) { return i; }
cyc_index_t cyc_get_coefficient(const cyc_entry_t& i) { return 1; }
cyc_entry_t cyc_make_entry(cyc_index_t _index, cyc_coefficient_t _value) { return cyc_entry_t(_index); }
void cyc_set_coefficient(cyc_entry_t& e, const cyc_coefficient_t c) {}

#endif

const cyc_entry_t& cyc_get_entry(const cyc_entry_t& e) { return e; }

typedef std::pair<cyc_value_t, cyc_index_t> cyc_diameter_index_t;
cyc_value_t cyc_get_diameter(const cyc_diameter_index_t& i) { return i.first; }
cyc_index_t cyc_get_index(const cyc_diameter_index_t& i) { return i.second; }

typedef std::pair<cyc_index_t, cyc_value_t> cyc_index_diameter_t;
cyc_index_t cyc_get_index(const cyc_index_diameter_t& i) { return i.first; }
cyc_value_t cyc_get_diameter(const cyc_index_diameter_t& i) { return i.second; }

struct cyc_diameter_entry_t : std::pair<cyc_value_t, cyc_entry_t> {
	using std::pair<cyc_value_t, cyc_entry_t>::pair;
	cyc_diameter_entry_t(cyc_value_t _diameter, cyc_index_t _index, cyc_coefficient_t _coefficient)
	    : cyc_diameter_entry_t(_diameter, cyc_make_entry(_index, _coefficient)) {}
	cyc_diameter_entry_t(const cyc_diameter_index_t& _diameter_index, cyc_coefficient_t _coefficient)
	    : cyc_diameter_entry_t(cyc_get_diameter(_diameter_index),
	                       cyc_make_entry(cyc_get_index(_diameter_index), _coefficient)) {}
	cyc_diameter_entry_t(const cyc_index_t& _index) : cyc_diameter_entry_t(0, _index, 0) {}
};

const cyc_entry_t& cyc_get_entry(const cyc_diameter_entry_t& p) { return p.second; }
cyc_entry_t& cyc_get_entry(cyc_diameter_entry_t& p) { return p.second; }
const cyc_index_t cyc_get_index(const cyc_diameter_entry_t& p) { return cyc_get_index(cyc_get_entry(p)); }
const cyc_coefficient_t cyc_get_coefficient(const cyc_diameter_entry_t& p) {
	return cyc_get_coefficient(cyc_get_entry(p));
}
const cyc_value_t& cyc_get_diameter(const cyc_diameter_entry_t& p) { return p.first; }
void cyc_set_coefficient(cyc_diameter_entry_t& p, const cyc_coefficient_t c) {
	cyc_set_coefficient(cyc_get_entry(p), c);
}

template <typename Entry> struct cyc_greater_diameter_or_smaller_index {
	bool operator()(const Entry& a, const Entry& b) {
		return (cyc_get_diameter(a) > cyc_get_diameter(b)) ||
		       ((cyc_get_diameter(a) == cyc_get_diameter(b)) && (cyc_get_index(a) < cyc_get_index(b)));
	}
};

template <typename Entry> struct cyc_smaller_diameter_or_greater_index {
	bool operator()(const Entry& a, const Entry& b) {
		return (cyc_get_diameter(a) < cyc_get_diameter(b)) ||
		       ((cyc_get_diameter(a) == cyc_get_diameter(b)) && (cyc_get_index(a) > cyc_get_index(b)));
	}
};

enum cyc_compressed_matrix_layout { cyc_LOWER_TRIANGULAR, cyc_UPPER_TRIANGULAR };

template <cyc_compressed_matrix_layout Layout> struct cyc_compressed_distance_matrix {
	std::vector<cyc_value_t> distances;
	std::vector<cyc_value_t*> rows;

	cyc_compressed_distance_matrix(std::vector<cyc_value_t>&& _distances)
	    : distances(std::move(_distances)), rows((1 + std::sqrt(1 + 8 * distances.size())) / 2) {
		assert(distances.size() == size() * (size() - 1) / 2);
		init_rows();
	}

	template <typename cyc_DistanceMatrix>
	cyc_compressed_distance_matrix(const cyc_DistanceMatrix& mat)
	    : distances(mat.size() * (mat.size() - 1) / 2), rows(mat.size()) {
		init_rows();

		for (size_t i = 1; i < size(); ++i)
			for (size_t j = 0; j < i; ++j) rows[i][j] = mat(i, j);
	}

	cyc_value_t operator()(const cyc_index_t i, const cyc_index_t j) const;
	size_t size() const { return rows.size(); }
	void init_rows();
};

typedef cyc_compressed_distance_matrix<cyc_LOWER_TRIANGULAR> cyc_compressed_lower_distance_matrix;
typedef cyc_compressed_distance_matrix<cyc_UPPER_TRIANGULAR> cyc_compressed_upper_distance_matrix;

template <> void cyc_compressed_lower_distance_matrix::init_rows() {
	cyc_value_t* pointer = &distances[0];
	for (size_t i = 1; i < size(); ++i) {
		rows[i] = pointer;
		pointer += i;
	}
}

template <> void cyc_compressed_upper_distance_matrix::init_rows() {
	cyc_value_t* pointer = &distances[0] - 1;
	for (size_t i = 0; i < size() - 1; ++i) {
		rows[i] = pointer;
		pointer += size() - i - 2;
	}
}

template <>
cyc_value_t cyc_compressed_lower_distance_matrix::operator()(const cyc_index_t i, const cyc_index_t j) const {
	return i == j ? 0 : i < j ? rows[j][i] : rows[i][j];
}

template <>
cyc_value_t cyc_compressed_upper_distance_matrix::operator()(const cyc_index_t i, const cyc_index_t j) const {
	return i == j ? 0 : i > j ? rows[j][i] : rows[i][j];
}

struct cyc_sparse_distance_matrix {
	std::vector<std::vector<cyc_index_diameter_t>> neighbors;
    std::vector<cyc_value_t> vertex_births;
	cyc_index_t num_edges;

	cyc_sparse_distance_matrix(std::vector<std::vector<cyc_index_diameter_t>>&& _neighbors,
	                       cyc_index_t _num_edges)
	    : neighbors(std::move(_neighbors)), num_edges(_num_edges) {}

	template <typename cyc_DistanceMatrix>
	cyc_sparse_distance_matrix(const cyc_DistanceMatrix& mat, const cyc_value_t threshold)
	    : neighbors(mat.size()), num_edges(0) {

		for (size_t i = 0; i < size(); ++i)
			for (size_t j = 0; j < size(); ++j)
				if (i != j && mat(i, j) <= threshold) {
					++num_edges;
					neighbors[i].push_back({j, mat(i, j)});
				}
	}

	cyc_value_t operator()(const cyc_index_t i, const cyc_index_t j) const {
		for (auto neighbor : neighbors[i])
			if (cyc_get_index(neighbor) == j) return cyc_get_diameter(neighbor);
		return std::numeric_limits<cyc_value_t>::infinity();
	}

	size_t size() const { return neighbors.size(); }


    mutable std::vector<std::vector<cyc_index_diameter_t>::const_reverse_iterator>
        neighbor_it;
    mutable std::vector<std::vector<cyc_index_diameter_t>::const_reverse_iterator>
        neighbor_end;

    // Initialize from COO format
    cyc_sparse_distance_matrix(int* I, int* J, cyc_value_t* V, int NEdges, int N,
                           const cyc_value_t threshold)
        : neighbors(N), vertex_births(N, 0), num_edges(0)
    {
        int i, j;
        cyc_value_t val;
        for (int idx = 0; idx < NEdges; idx++) {
            i = I[idx];
            j = J[idx];
            val = V[idx];
            if (i < j && val <= threshold) {
                neighbors[i].push_back(std::make_pair(j, val));
                neighbors[j].push_back(std::make_pair(i, val));
                ++num_edges;
            } else if (i == j) {
                vertex_births[i] = val;
            }
        }

        for (size_t i = 0; i < neighbors.size(); ++i)
            std::sort(neighbors[i].begin(), neighbors[i].end());
    }

};

struct cyc_euclidean_distance_matrix {
	std::vector<std::vector<cyc_value_t>> points;

	cyc_euclidean_distance_matrix(std::vector<std::vector<cyc_value_t>>&& _points)
	    : points(std::move(_points)) {
		for (auto p : points) { assert(p.size() == points.front().size()); }
	}

	cyc_value_t operator()(const cyc_index_t i, const cyc_index_t j) const {
		assert(i < points.size());
		assert(j < points.size());
		return std::sqrt(std::inner_product(
		    points[i].begin(), points[i].end(), points[j].begin(), cyc_value_t(), std::plus<cyc_value_t>(),
		    [](cyc_value_t u, cyc_value_t v) { return (u - v) * (u - v); }));
	}

	size_t size() const { return points.size(); }
};

class cyc_union_find {
	std::vector<cyc_index_t> parent;
	std::vector<uint8_t> rank;
    std::vector<cyc_value_t> birth;

public:
	cyc_union_find(const cyc_index_t n) : parent(n), rank(n, 0), birth(n, 0) {
		std::cout << "Entered union_find";
		for (cyc_index_t i = 0; i < n; ++i) parent[i] = i;
	}
    
	void set_birth(cyc_index_t i, cyc_value_t val) { birth[i] = val; }

    cyc_value_t get_birth(cyc_index_t i) { 
		return birth[i]; 
	}

	cyc_index_t find(cyc_index_t x) {
		cyc_index_t y = x, z;
		while ((z = parent[y]) != y) y = z;
		while ((z = parent[x]) != y) {
			parent[x] = y;
			x = z;
		}
		return z;
	}

	void link(cyc_index_t x, cyc_index_t y) {
		if ((x = find(x)) == (y = find(y))) return;
		if (rank[x] > rank[y]) {
            parent[y] = x;
            birth[x] = std::min(birth[x], birth[y]);  // Elder rule
        }
		else {
			parent[x] = y;
            birth[y] = std::min(birth[x], birth[y]);  // Elder rule
			if (rank[x] == rank[y]) ++rank[y];
		}
	}
};

template <typename T> T begin(std::pair<T, T>& p) { return p.first; }
template <typename T> T end(std::pair<T, T>& p) { return p.second; }

template <typename ValueType> class cyc_compressed_sparse_matrix {
	std::vector<size_t> bounds;
	std::vector<ValueType> entries;

	typedef typename std::vector<ValueType>::iterator iterator;
	typedef std::pair<iterator, iterator> iterator_pair;

public:
	size_t size() const { return bounds.size(); }

	iterator_pair subrange(const cyc_index_t index) {
		return {entries.begin() + (index == 0 ? 0 : bounds[index - 1]),
		        entries.begin() + bounds[index]};
	}

	void append_column() { bounds.push_back(entries.size()); }

	void push_back(const ValueType e) {
		assert(0 < size());
		entries.push_back(e);
		++bounds.back();
	}
};

template <class cyc_Predicate>
cyc_index_t cyc_get_max(cyc_index_t top, const cyc_index_t bottom, const cyc_Predicate pred) {
	if (!pred(top)) {
		cyc_index_t count = top - bottom;
		while (count > 0) {
			cyc_index_t step = count >> 1, mid = top - step;
			if (!pred(mid)) {
				top = mid - 1;
				count -= step + 1;
			} else
				count = step;
		}
	}
	return top;
}


/* This is the data structure from which the results of running ripser can be
 * returned */
struct ripserResultsCycles {
    /* The first variable is a vector of unrolled persistence diagrams
       so, for example births_and_deaths_by_dim[0] contains a list of
                [birth0, death0, birth1, death1, ..., birthk, deathk]
       for k points in the 0D persistence diagram
       and likewise for d-dimensional persistence in births_and_deaths_by_dim[d]
    */
    std::vector<std::vector<cyc_value_t>> births_and_deaths_by_dim;
	std::vector<cyc_index_t> dim_0_pairs;
    /*
      The second variable is a vector of representative cocycles for each
      dimension. For now, only cocycles above dimension 0 are added, so
      dimension 0 is an empty list For the others, cocycles_by_dim[d] holds an
      array of representative cocycles for dimension d which is parallel with
      the array of births/deaths for dimension d. Each element of the array is
      itself an array of unrolled information about the cocycle For dimension 1,
      for example, the zeroeth element of the array contains [ccl0_simplex0_idx0
      ccl0_simplex0_idx1 ccl0_simplex0_val, ccl0_simplex1_idx0
      ccl0_simplex1_idx1 ccl0_simplex1_val, ... ccl0_simplexk_idx0
      ccl0_simplexk_idx1 ccl0_simplexk_val] for a cocycle representing the first
      persistence point, which has k simplices with nonzero values in the
      representative cocycle
    */
    std::vector<std::vector<std::vector<long>>> cycles_by_dim;
    /* The third variable is the number of edges that were added during the
     * computation*/
    int num_edges;
};

template <typename cyc_DistanceMatrix> class cyc_ripser {
	const cyc_DistanceMatrix dist;
	const cyc_index_t n, dim_max;
	const cyc_value_t threshold;
	const float ratio;
	const cyc_coefficient_t modulus;
	const cyc_binomial_coeff_table binomial_coeff;
	const std::vector<cyc_coefficient_t> multiplicative_inverse;
	mutable std::vector<cyc_diameter_entry_t> cofacet_entries;
	mutable std::vector<cyc_index_t> vertices;

	struct entry_hash {
		std::size_t operator()(const cyc_entry_t& e) const { return cyc_hash<cyc_index_t>()(::cyc_get_index(e)); }
	};

	struct equal_index {
		bool operator()(const cyc_entry_t& e, const cyc_entry_t& f) const {
			return ::cyc_get_index(e) == ::cyc_get_index(f);
		}
	};

	typedef cyc_hash_map<cyc_entry_t, size_t, entry_hash, equal_index> entry_cyc_hash_map;

public:
    mutable std::vector<std::vector<cyc_value_t>> births_and_deaths_by_dim;
    mutable std::vector<std::vector<std::vector<long>>> cycles_by_dim;
	mutable std::vector<cyc_index_t> cyc_dim_0_pairs;

	cyc_ripser(cyc_DistanceMatrix&& _dist, cyc_index_t _dim_max, cyc_value_t _threshold, float _ratio,
	       cyc_coefficient_t _modulus)
	    : dist(std::move(_dist)), n(dist.size()),
	      dim_max(std::min(_dim_max, cyc_index_t(dist.size() - 2))), threshold(_threshold),
	      ratio(_ratio), modulus(_modulus), binomial_coeff(n, dim_max + 2),
	      multiplicative_inverse(cyc_multiplicative_inverse_vector(_modulus)) {}

	cyc_index_t cyc_get_max_vertex(const cyc_index_t idx, const cyc_index_t k, const cyc_index_t n) const {
		return cyc_get_max(n, k - 1, [&](cyc_index_t w) -> bool { return (binomial_coeff(w, k) <= idx); });
	}

	cyc_index_t cyc_get_edge_index(const cyc_index_t i, const cyc_index_t j) const {
		return binomial_coeff(i, 2) + j;
	}

    void cyc_copy_results(ripserResultsCycles& res)
    {
        res.births_and_deaths_by_dim = births_and_deaths_by_dim;
        res.cycles_by_dim = cycles_by_dim;
		res.dim_0_pairs = cyc_dim_0_pairs;
    }

	template <typename OutputIterator>
	OutputIterator cyc_get_simplex_vertices(cyc_index_t idx, const cyc_index_t dim, cyc_index_t n,
	                                    OutputIterator out) const {
		--n;
		for (cyc_index_t k = dim + 1; k > 0; --k) {
			n = cyc_get_max_vertex(idx, k, n);
			*out++ = n;
			idx -= binomial_coeff(n, k);
		}
		return out;
	}

	cyc_value_t compute_diameter(const cyc_index_t index, cyc_index_t dim) const {
		cyc_value_t diam = -std::numeric_limits<cyc_value_t>::infinity();

		vertices.clear();
		cyc_get_simplex_vertices(index, dim, dist.size(), std::back_inserter(vertices));

		for (cyc_index_t i = 0; i <= dim; ++i)
			for (cyc_index_t j = 0; j < i; ++j) {
				diam = std::max(diam, dist(vertices[i], vertices[j]));
			}
		return diam;
	}

	class cyc_simplex_coboundary_enumerator;

	class cyc_simplex_boundary_enumerator {
	private:
		cyc_index_t idx_below, idx_above, j, k;
		const cyc_diameter_entry_t simplex;
		const cyc_coefficient_t modulus;
		const cyc_binomial_coeff_table& binomial_coeff;
		const cyc_index_t dim;
		const cyc_ripser& parent;

	public:
		cyc_simplex_boundary_enumerator(const cyc_diameter_entry_t _simplex, const cyc_index_t _dim,
		                            const cyc_ripser& _parent)
		    : idx_below(cyc_get_index(_simplex)), idx_above(0), j(_parent.n - 1), k(_dim),
		      simplex(_simplex), modulus(_parent.modulus), binomial_coeff(_parent.binomial_coeff),
		      dim(_dim), parent(_parent) {}

		bool has_next() { return (k >= 0); }

		cyc_diameter_entry_t next() {
			j = parent.cyc_get_max_vertex(idx_below, k + 1, j);

			cyc_index_t face_index = idx_above - binomial_coeff(j, k + 1) + idx_below;

			cyc_value_t face_diameter = parent.compute_diameter(face_index, dim - 1);

			cyc_coefficient_t face_coefficient =
			    (k & 1 ? -1 + modulus : 1) * cyc_get_coefficient(simplex) % modulus;

			idx_below -= binomial_coeff(j, k + 1);
			idx_above += binomial_coeff(j, k);

			--k;

			return cyc_diameter_entry_t(face_diameter, face_index, face_coefficient);
		}
	};

	void cyc_assemble_columns_to_reduce(std::vector<cyc_diameter_index_t>& simplices,
	                                std::vector<cyc_diameter_index_t>& columns_to_reduce,
	                                entry_cyc_hash_map& pivot_column_index, cyc_index_t dim) {

#ifdef INDICATE_PROGRESS
		std::cerr << cyc_clear_line << "assembling columns" << std::flush;
		std::chrono::steady_clock::time_point next = std::chrono::steady_clock::now() + time_step;
#endif

		--dim;
		columns_to_reduce.clear();
		std::vector<cyc_diameter_index_t> next_simplices;

		for (cyc_diameter_index_t& simplex : simplices) {
			cyc_simplex_coboundary_enumerator cofacets(cyc_diameter_entry_t(simplex, 1), dim, *this);

			while (cofacets.has_next(false)) {
#ifdef INDICATE_PROGRESS
				if (std::chrono::steady_clock::now() > next) {
					std::cerr << cyc_clear_line << "assembling " << next_simplices.size()
					          << " columns (processing " << std::distance(&simplices[0], &simplex)
					          << "/" << simplices.size() << " simplices)" << std::flush;
					next = std::chrono::steady_clock::now() + time_step;
				}
#endif
				auto cofacet = cofacets.next();
				if (cyc_get_diameter(cofacet) <= threshold) {

					next_simplices.push_back({cyc_get_diameter(cofacet), cyc_get_index(cofacet)});

					if (pivot_column_index.find(cyc_get_entry(cofacet)) == pivot_column_index.end())
						columns_to_reduce.push_back({cyc_get_diameter(cofacet), cyc_get_index(cofacet)});
				}
			}
		}

		simplices.swap(next_simplices);

#ifdef INDICATE_PROGRESS
		std::cerr << cyc_clear_line << "sorting " << columns_to_reduce.size() << " columns"
		          << std::flush;
#endif

		std::sort(columns_to_reduce.begin(), columns_to_reduce.end(),
		          cyc_greater_diameter_or_smaller_index<cyc_diameter_index_t>());
#ifdef INDICATE_PROGRESS
		std::cerr << cyc_clear_line << std::flush;
#endif
	}
	
	cyc_value_t cyc_get_vertex_birth(cyc_index_t i);
	void cyc_compute_dim_0_pairs(std::vector<cyc_diameter_index_t>& edges,
	                         std::vector<cyc_diameter_index_t>& columns_to_reduce) {
#ifdef PRINT_PERSISTENCE_PAIRS
		std::cout << "persistence intervals in dim 0:" << std::endl;
#endif

		cyc_union_find dset(n);

		std::cout << "Instantiated union_find" << std::endl;
		for (cyc_index_t i = 0; i < n; i++) {
            dset.set_birth(i, cyc_get_vertex_birth(i));
        }
		
		std::cout << "Entered union_find" << std::endl;
		std::cout << "Calculating Edges" << std::endl;
		edges = cyc_get_edges();
		std::sort(edges.rbegin(), edges.rend(),
		          cyc_greater_diameter_or_smaller_index<cyc_diameter_index_t>());

		std::vector<cyc_index_t> vertices_of_edge(2);
		std::cout << "Calculated Edges" << std::endl;
		std::cout << "Calculating cycle pairs" << std::endl;
		for (auto e : edges) {
			std::cout << "Calculating vertices of simplex" << std::endl;
			cyc_get_simplex_vertices(cyc_get_index(e), 1, n, vertices_of_edge.rbegin());
			std::cout << "Finding u" << std::endl;
			cyc_index_t u = dset.find(vertices_of_edge[0]), v = dset.find(vertices_of_edge[1]);

			if (u != v) {
				if (cyc_get_diameter(e) != 0) {

                    cyc_value_t birth = std::max(dset.get_birth(u), dset.get_birth(v));
                    cyc_value_t death = cyc_get_diameter(e);

                    if (death > birth) {
                        births_and_deaths_by_dim[0].push_back(birth);
                        births_and_deaths_by_dim[0].push_back(death);
                    }

					cyc_dim_0_pairs.push_back(u);
					cyc_dim_0_pairs.push_back(v);
					
                }
				dset.link(u, v);
			} else
				columns_to_reduce.push_back(e);
		}
		
		std::reverse(columns_to_reduce.begin(), columns_to_reduce.end());
		std::cout << "Columns Calculated and reversed" << std::endl;
		
		for (cyc_index_t i = 0; i < n; ++i)
			if (dset.find(i) == i) {
                births_and_deaths_by_dim[0].push_back(dset.get_birth(i));
                births_and_deaths_by_dim[0].push_back(
                    std::numeric_limits<cyc_value_t>::infinity());
            }
	}

	template <typename Chain> std::vector<long> print_chain(Chain& cycle, cyc_index_t dim) {
		cyc_diameter_entry_t e;
        std::vector<long> current_chain;

		// std::cout << "{";
		while (cyc_get_index(e = cyc_get_pivot(cycle)) != -1) {
			vertices.resize(dim + 1);
			cyc_get_simplex_vertices(cyc_get_index(e), dim, n, vertices.rbegin());

			// std::cout << "[";
			auto it = vertices.begin();
			if (it != vertices.end()) {
			    current_chain.push_back(*it++);
				while (it != vertices.end()) {
                    current_chain.push_back(*it++);
                } 
			}

			cycle.pop();
        }

        return current_chain;
	}

	template <typename Column> cyc_diameter_entry_t cyc_pop_pivot(Column& column) {
		cyc_diameter_entry_t pivot(-1);
#ifdef USE_COEFFICIENTS
		while (!column.empty()) {
			if (cyc_get_coefficient(pivot) == 0)
				pivot = column.top();
			else if (cyc_get_index(column.top()) != cyc_get_index(pivot))
				return pivot;
			else
				cyc_set_coefficient(pivot,
				                (cyc_get_coefficient(pivot) + cyc_get_coefficient(column.top())) % modulus);
			column.pop();
		}
		return (cyc_get_coefficient(pivot) == 0) ? -1 : pivot;
#else
		while (!column.empty()) {
			pivot = column.top();
			column.pop();
			if (column.empty() || cyc_get_index(column.top()) != cyc_get_index(pivot)) return pivot;
			column.pop();
		}
		return -1;
#endif
	}

	template <typename Column> cyc_diameter_entry_t cyc_get_pivot(Column& column) {
		cyc_diameter_entry_t result = cyc_pop_pivot(column);
		if (cyc_get_index(result) != -1) column.push(result);
		return result;
	}

	template <typename BoundaryEnumerator, typename Column>
	cyc_diameter_entry_t cyc_init_coboundary_and_get_pivot(const cyc_diameter_entry_t simplex,
	                                               Column& working_coboundary, const cyc_index_t& dim,
	                                               entry_cyc_hash_map& pivot_column_index) {
		bool check_for_emergent_pair = true;
		cofacet_entries.clear();
		BoundaryEnumerator cofacets(simplex, dim, *this);
		while (cofacets.has_next()) {
			cyc_diameter_entry_t cofacet = cofacets.next();
			if (cyc_get_diameter(cofacet) <= threshold) {
				cofacet_entries.push_back(cofacet);
				if (check_for_emergent_pair && (cyc_get_diameter(simplex) == cyc_get_diameter(cofacet))) {
					if (pivot_column_index.find(cyc_get_entry(cofacet)) == pivot_column_index.end())
						return cofacet;
					check_for_emergent_pair = false;
				}
			}
		}
		for (auto cofacet : cofacet_entries) working_coboundary.push(cofacet);
		return cyc_get_pivot(working_coboundary);
	}

	template <typename BoundaryEnumerator, typename Column>
	void add_simplex_coboundary(const cyc_diameter_entry_t simplex, const cyc_index_t& dim,
	                            Column& working_reduction_column, Column& working_coboundary) {
		working_reduction_column.push(simplex);
		BoundaryEnumerator cofacets(simplex, dim, *this);
		while (cofacets.has_next()) {
			cyc_diameter_entry_t cofacet = cofacets.next();
			if (cyc_get_diameter(cofacet) <= threshold) working_coboundary.push(cofacet);
		}
	}

	template <typename BoundaryEnumerator, typename Column>
	void add_coboundary(cyc_compressed_sparse_matrix<cyc_diameter_entry_t>& reduction_matrix,
	                    const std::vector<cyc_diameter_index_t>& columns_to_reduce,
	                    const size_t index_column_to_add, const cyc_coefficient_t factor,
	                    const size_t& dim, Column& working_reduction_column,
	                    Column& working_coboundary) {
		cyc_diameter_entry_t column_to_add(columns_to_reduce[index_column_to_add], factor);
		add_simplex_coboundary<BoundaryEnumerator>(column_to_add, dim, working_reduction_column,
		                                           working_coboundary);

		for (cyc_diameter_entry_t simplex : reduction_matrix.subrange(index_column_to_add)) {
			cyc_set_coefficient(simplex, cyc_get_coefficient(simplex) * factor % modulus);
			add_simplex_coboundary<BoundaryEnumerator>(simplex, dim, working_reduction_column,
			                                           working_coboundary);
		}
	}

	template <typename BoundaryEnumerator, typename Sorter, bool cohomology = true>
	void compute_pairs(const std::vector<cyc_diameter_index_t>& columns_to_reduce,
	                   entry_cyc_hash_map& pivot_column_index, const cyc_index_t dim) {

#ifdef PRINT_PERSISTENCE_PAIRS
		if (!cohomology)
			std::cout << "persistence intervals in dim " << dim - 1 << ":" << std::endl;
#endif

		cyc_compressed_sparse_matrix<cyc_diameter_entry_t> reduction_matrix;

#ifdef INDICATE_PROGRESS
		std::chrono::steady_clock::time_point next = std::chrono::steady_clock::now() + time_step;
#endif
		std::cout << "Num cols: " << columns_to_reduce.size() << std::endl;
		for (size_t index_column_to_reduce = 0; index_column_to_reduce < columns_to_reduce.size();
		     ++index_column_to_reduce) {

			cyc_diameter_entry_t column_to_reduce(columns_to_reduce[index_column_to_reduce], 1);
			cyc_value_t diameter = cyc_get_diameter(column_to_reduce);

			reduction_matrix.append_column();

			std::priority_queue<cyc_diameter_entry_t, std::vector<cyc_diameter_entry_t>, Sorter>
			    working_reduction_column, working_coboundary, final_coboundary;

			cyc_diameter_entry_t pivot = cyc_init_coboundary_and_get_pivot<BoundaryEnumerator>(
			    column_to_reduce, working_coboundary, dim, pivot_column_index);
			
			std::cout << "Init boundary and get pivot" << std::endl;

			while (true) {
#ifdef INDICATE_PROGRESS
				if (std::chrono::steady_clock::now() > next) {
					std::cerr << cyc_clear_line << "reducing column " << index_column_to_reduce + 1
					          << "/" << columns_to_reduce.size() << " (diameter " << diameter << ")"
					          << std::flush;
					next = std::chrono::steady_clock::now() + time_step;
				}
#endif
				if (cyc_get_index(pivot) != -1) {
					auto pair = pivot_column_index.find(cyc_get_entry(pivot));
					if (pair != pivot_column_index.end()) {
						cyc_entry_t other_pivot = pair->first;
						cyc_index_t index_column_to_add = pair->second;
						cyc_coefficient_t factor =
						    modulus - cyc_get_coefficient(pivot) *
						                  multiplicative_inverse[cyc_get_coefficient(other_pivot)] %
						                  modulus;

						add_coboundary<BoundaryEnumerator>(
						    reduction_matrix, columns_to_reduce, index_column_to_add, factor, dim,
						    working_reduction_column, working_coboundary);

						pivot = cyc_get_pivot(working_coboundary);
					} else {
                        cyc_value_t death = cyc_get_diameter(pivot);
                        if (death > diameter * ratio) {
                            births_and_deaths_by_dim[dim].push_back(diameter);
                            births_and_deaths_by_dim[dim].push_back(death);
                        }

						if (final_coboundary.empty()) {
							pivot_column_index.insert({cyc_get_entry(pivot), index_column_to_reduce});

							while (true) {
								cyc_diameter_entry_t e = cyc_pop_pivot(working_reduction_column);
								if (cyc_get_index(e) == -1) break;
								assert(cyc_get_coefficient(e) > 0);
								reduction_matrix.push_back(e);
							}

							cyc_value_t birth = cyc_get_diameter(pivot);
							if (cohomology || (birth * ratio >= diameter)) break;
						}

						final_coboundary.push(cyc_pop_pivot(working_coboundary));
						pivot = cyc_get_pivot(working_coboundary);
					}
				} else {
					if (final_coboundary.empty()) {

						std::cout << "+[" << diameter << ", ):  ";
                        std::vector<long> current_chain = print_chain(working_reduction_column, dim);
                        cycles_by_dim[dim].push_back(current_chain);

					} else {
						pivot = cyc_get_pivot(final_coboundary);
						cyc_value_t death = cyc_get_diameter(pivot);
						if (diameter > death * ratio) {
                            births_and_deaths_by_dim[dim].push_back(diameter);
							births_and_deaths_by_dim[dim].push_back(std::numeric_limits<cyc_value_t>::infinity());
							std::vector<long> final_chain = print_chain(final_coboundary, dim - 1);
							cycles_by_dim[dim].push_back(final_chain);
						}
					}
					break;
				}
			}
		}

		std::cout << "Ended loop";
#ifdef INDICATE_PROGRESS
		std::cerr << cyc_clear_line << std::flush;
#endif
	}

	std::vector<cyc_diameter_index_t> cyc_get_edges();

	void cyc_compute_barcodes() {
		std::vector<cyc_diameter_index_t> simplices, columns_to_reduce;
        
        births_and_deaths_by_dim.resize(dim_max + 2);
        cycles_by_dim.resize(dim_max + 2);

		cyc_compute_dim_0_pairs(simplices, columns_to_reduce);

		for (cyc_index_t dim = 1; dim <= dim_max; ++dim) {
			entry_cyc_hash_map pivot_column_index;
			pivot_column_index.reserve(columns_to_reduce.size());

			compute_pairs<cyc_simplex_coboundary_enumerator,
			              cyc_greater_diameter_or_smaller_index<cyc_diameter_entry_t>>(
			    columns_to_reduce, pivot_column_index, dim);

			std::vector<cyc_diameter_index_t> boundary_columns_to_reduce;

			std::cout << "Exited compute_pairs";

			for (auto it = pivot_column_index.begin(); it != pivot_column_index.end(); ++it) {
				auto pair = *it;
				std::cout << "Entered loop";
				cyc_index_t pivot_row_index = cyc_get_index(pair.first);
				boundary_columns_to_reduce.push_back(
				    std::make_pair(compute_diameter(pivot_row_index, dim + 1), pivot_row_index));

				// TODO: essential indices missing (required for thresholding)
			}

			std::cout << "Computed Boundary Columns" << std::endl;
			
			std::sort(boundary_columns_to_reduce.rbegin(), boundary_columns_to_reduce.rend(),
			          cyc_greater_diameter_or_smaller_index<cyc_diameter_index_t>());

			std::cout << "Sorted Boundary Columns" << std::endl;

			entry_cyc_hash_map boundary_pivot_column_index;
			boundary_pivot_column_index.reserve(boundary_columns_to_reduce.size());

			std::cout << "Entering compute_pairs for the second time" << std::endl;

			compute_pairs<cyc_simplex_boundary_enumerator,
			              cyc_smaller_diameter_or_greater_index<cyc_diameter_entry_t>, false>(
			    boundary_columns_to_reduce, boundary_pivot_column_index, dim + 1);

			std::cout << "Pairs computed";

			if (dim <= dim_max) {
				cyc_assemble_columns_to_reduce(simplices, columns_to_reduce, pivot_column_index,
				                           dim + 1);
			}
		}

		std::cout << "Barcodes computed";
	}
};

template <>
cyc_value_t cyc_ripser<cyc_compressed_lower_distance_matrix>::cyc_get_vertex_birth(cyc_index_t i)
{
    // TODO: Dummy for now; nonzero vertex births are only done through
    // sparse matrices at the moment
    return 0.0;
}

template <>
cyc_value_t cyc_ripser<cyc_sparse_distance_matrix>::cyc_get_vertex_birth(cyc_index_t i)
{
    return dist.vertex_births[i];
}

template <> class cyc_ripser<cyc_compressed_lower_distance_matrix>::cyc_simplex_coboundary_enumerator {
	cyc_index_t idx_below, idx_above, j, k;
	std::vector<cyc_index_t> vertices;
	const cyc_diameter_entry_t simplex;
	const cyc_coefficient_t modulus;
	const cyc_compressed_lower_distance_matrix& dist;
	const cyc_binomial_coeff_table& binomial_coeff;

public:
	cyc_simplex_coboundary_enumerator(const cyc_diameter_entry_t _simplex, const cyc_index_t _dim,
	                              const cyc_ripser& parent)
	    : idx_below(cyc_get_index(_simplex)), idx_above(0), j(parent.n - 1), k(_dim + 1),
	      vertices(_dim + 1), simplex(_simplex), modulus(parent.modulus), dist(parent.dist),
	      binomial_coeff(parent.binomial_coeff) {
		parent.cyc_get_simplex_vertices(cyc_get_index(_simplex), _dim, parent.n, vertices.rbegin());
	}

	bool has_next(bool all_cofacets = true) {
		return (j >= k && (all_cofacets || binomial_coeff(j, k) > idx_below));
	}

	cyc_diameter_entry_t next() {
		while ((binomial_coeff(j, k) <= idx_below)) {
			idx_below -= binomial_coeff(j, k);
			idx_above += binomial_coeff(j, k + 1);
			--j;
			--k;
			assert(k != -1);
		}
		cyc_value_t cofacet_diameter = cyc_get_diameter(simplex);
		for (cyc_index_t i : vertices) cofacet_diameter = std::max(cofacet_diameter, dist(j, i));
		cyc_index_t cofacet_index = idx_above + binomial_coeff(j--, k + 1) + idx_below;
		cyc_coefficient_t cofacet_coefficient =
		    (k & 1 ? modulus - 1 : 1) * cyc_get_coefficient(simplex) % modulus;
		return cyc_diameter_entry_t(cofacet_diameter, cofacet_index, cofacet_coefficient);
	}
};

template <> class cyc_ripser<cyc_sparse_distance_matrix>::cyc_simplex_coboundary_enumerator {
	cyc_index_t idx_below, idx_above, k;
	std::vector<cyc_index_t> vertices;
	const cyc_diameter_entry_t simplex;
	const cyc_coefficient_t modulus;
	const cyc_sparse_distance_matrix& dist;
	const cyc_binomial_coeff_table& binomial_coeff;
	std::vector<std::vector<cyc_index_diameter_t>::const_reverse_iterator> neighbor_it;
	std::vector<std::vector<cyc_index_diameter_t>::const_reverse_iterator> neighbor_end;
	cyc_index_diameter_t neighbor;

public:
	cyc_simplex_coboundary_enumerator(const cyc_diameter_entry_t _simplex, const cyc_index_t _dim,
	                              const cyc_ripser& _parent)
	    : idx_below(cyc_get_index(_simplex)), idx_above(0), k(_dim + 1), vertices(_dim + 1),
	      simplex(_simplex), modulus(_parent.modulus), dist(_parent.dist),
	      binomial_coeff(_parent.binomial_coeff) {
		_parent.cyc_get_simplex_vertices(idx_below, _dim, _parent.n, vertices.rbegin());

		for (auto v : vertices) {
			neighbor_it.push_back(dist.neighbors[v].rbegin());
			neighbor_end.push_back(dist.neighbors[v].rend());
		}
	}

	bool has_next(bool all_cofacets = true) {
		for (auto &it0 = neighbor_it[0], &end0 = neighbor_end[0]; it0 != end0; ++it0) {
			neighbor = *it0;
			for (size_t idx = 1; idx < neighbor_it.size(); ++idx) {
				auto &it = neighbor_it[idx], end = neighbor_end[idx];
				while (cyc_get_index(*it) > cyc_get_index(neighbor))
					if (++it == end) return false;
				if (cyc_get_index(*it) != cyc_get_index(neighbor))
					goto continue_outer;
				else
					neighbor = std::max(neighbor, *it);
			}
			while (k > 0 && vertices[k - 1] > cyc_get_index(neighbor)) {
				if (!all_cofacets) return false;
				idx_below -= binomial_coeff(vertices[k - 1], k);
				idx_above += binomial_coeff(vertices[k - 1], k + 1);
				--k;
			}
			return true;
		continue_outer:;
		}
		return false;
	}

	cyc_diameter_entry_t next() {
		++neighbor_it[0];
		cyc_value_t cofacet_diameter = std::max(cyc_get_diameter(simplex), cyc_get_diameter(neighbor));
		cyc_index_t cofacet_index = idx_above + binomial_coeff(cyc_get_index(neighbor), k + 1) + idx_below;
		cyc_coefficient_t cofacet_coefficient =
		    (k & 1 ? modulus - 1 : 1) * cyc_get_coefficient(simplex) % modulus;
		return cyc_diameter_entry_t(cofacet_diameter, cofacet_index, cofacet_coefficient);
	}
};

template <> std::vector<cyc_diameter_index_t> cyc_ripser<cyc_compressed_lower_distance_matrix>::cyc_get_edges() {
	std::vector<cyc_diameter_index_t> edges;
	std::vector<cyc_index_t> vertices(2);
	for (cyc_index_t index = binomial_coeff(n, 2); index-- > 0;) {
		cyc_get_simplex_vertices(index, 1, dist.size(), vertices.rbegin());
		cyc_value_t length = dist(vertices[0], vertices[1]);
		if (length <= threshold) edges.push_back({length, index});
	}
	return edges;
}

template <> std::vector<cyc_diameter_index_t> cyc_ripser<cyc_sparse_distance_matrix>::cyc_get_edges() {
	std::vector<cyc_diameter_index_t> edges;
	for (cyc_index_t i = 0; i < n; ++i)
		for (auto n : dist.neighbors[i]) {
			cyc_index_t j = cyc_get_index(n);
			if (i > j) edges.push_back({cyc_get_diameter(n), cyc_get_edge_index(i, j)});
		}
	return edges;
}

enum file_format {
	LOWER_DISTANCE_MATRIX,
	UPPER_DISTANCE_MATRIX,
	DISTANCE_MATRIX,
	POINT_CLOUD,
	DIPHA,
	SPARSE,
	BINARY
};

static const uint16_t endian_check(0xff00);
static const bool is_big_endian = *reinterpret_cast<const uint8_t*>(&endian_check);

template <typename T> T read(std::istream& input_stream) {
	T result;
	char* p = reinterpret_cast<char*>(&result);
	if (input_stream.read(p, sizeof(T)).gcount() != sizeof(T)) return T();
	if (is_big_endian) std::reverse(p, p + sizeof(T));
	return result;
}

cyc_compressed_lower_distance_matrix cyc_read_point_cloud(std::istream& input_stream) {
	std::vector<std::vector<cyc_value_t>> points;

	std::string line;
	cyc_value_t value;
	while (std::getline(input_stream, line)) {
		std::vector<cyc_value_t> point;
		std::istringstream s(line);
		while (s >> value) {
			point.push_back(value);
			s.ignore();
		}
		if (!point.empty()) points.push_back(point);
		assert(point.size() == points.front().size());
	}

	cyc_euclidean_distance_matrix eucl_dist(std::move(points));
	cyc_index_t n = eucl_dist.size();
	// std::cout << "point cloud with " << n << " points in dimension "
	//           << eucl_dist.points.front().size() << std::endl;

	std::vector<cyc_value_t> distances;
	for (int i = 0; i < n; ++i)
		for (int j = 0; j < i; ++j) distances.push_back(eucl_dist(i, j));

	return cyc_compressed_lower_distance_matrix(std::move(distances));
}

cyc_sparse_distance_matrix cyc_read_sparse_distance_matrix(std::istream& input_stream) {
	std::vector<std::vector<cyc_index_diameter_t>> neighbors;
	cyc_index_t num_edges = 0;

	std::string line;
	while (std::getline(input_stream, line)) {
		std::istringstream s(line);
		size_t i, j;
		cyc_value_t value;
		s >> i;
		s >> j;
		s >> value;
		if (i != j) {
			neighbors.resize(std::max({neighbors.size(), i + 1, j + 1}));
			neighbors[i].push_back({j, value});
			neighbors[j].push_back({i, value});
			++num_edges;
		}
	}

	for (size_t i = 0; i < neighbors.size(); ++i)
		std::sort(neighbors[i].begin(), neighbors[i].end());

	return cyc_sparse_distance_matrix(std::move(neighbors), num_edges);
}

cyc_compressed_lower_distance_matrix cyc_read_lower_distance_matrix(std::istream& input_stream) {
	std::vector<cyc_value_t> distances;
	cyc_value_t value;
	while (input_stream >> value) {
		distances.push_back(value);
		input_stream.ignore();
	}

	return cyc_compressed_lower_distance_matrix(std::move(distances));
}

cyc_compressed_lower_distance_matrix cyc_read_upper_distance_matrix(std::istream& input_stream) {
	std::vector<cyc_value_t> distances;
	cyc_value_t value;
	while (input_stream >> value) {
		distances.push_back(value);
		input_stream.ignore();
	}

	return cyc_compressed_lower_distance_matrix(cyc_compressed_upper_distance_matrix(std::move(distances)));
}

cyc_compressed_lower_distance_matrix cyc_read_distance_matrix(std::istream& input_stream) {
	std::vector<cyc_value_t> distances;

	std::string line;
	cyc_value_t value;
	for (int i = 0; std::getline(input_stream, line); ++i) {
		std::istringstream s(line);
		for (int j = 0; j < i && s >> value; ++j) {
			distances.push_back(value);
			s.ignore();
		}
	}

	return cyc_compressed_lower_distance_matrix(std::move(distances));
}

cyc_compressed_lower_distance_matrix cyc_read_dipha(std::istream& input_stream) {
	if (read<int64_t>(input_stream) != 8067171840) {
		std::cerr << "input is not a Dipha file (magic number: 8067171840)" << std::endl;
		exit(-1);
	}

	if (read<int64_t>(input_stream) != 7) {
		std::cerr << "input is not a Dipha distance matrix (file type: 7)" << std::endl;
		exit(-1);
	}

	cyc_index_t n = read<int64_t>(input_stream);

	std::vector<cyc_value_t> distances;

	for (int i = 0; i < n; ++i)
		for (int j = 0; j < n; ++j)
			if (i > j)
				distances.push_back(read<double>(input_stream));
			else
				read<double>(input_stream);

	return cyc_compressed_lower_distance_matrix(std::move(distances));
}

cyc_compressed_lower_distance_matrix read_binary(std::istream& input_stream) {
	std::vector<cyc_value_t> distances;
	while (!input_stream.eof()) distances.push_back(read<cyc_value_t>(input_stream));
	return cyc_compressed_lower_distance_matrix(std::move(distances));
}

cyc_compressed_lower_distance_matrix read_file(std::istream& input_stream, const file_format format) {
	switch (format) {
	case LOWER_DISTANCE_MATRIX:
		return cyc_read_lower_distance_matrix(input_stream);
	case UPPER_DISTANCE_MATRIX:
		return cyc_read_upper_distance_matrix(input_stream);
	case DISTANCE_MATRIX:
		return cyc_read_distance_matrix(input_stream);
	case POINT_CLOUD:
		return cyc_read_point_cloud(input_stream);
	case DIPHA:
		return cyc_read_dipha(input_stream);
	default:
		return read_binary(input_stream);
	}
}

void print_usage_and_exit(int exit_code) {
	std::cerr
	    << "Usage: "
	    << "ripser "
	    << "[options] [filename]" << std::endl
	    << std::endl
	    << "Options:" << std::endl
	    << std::endl
	    << "  --help           print this screen" << std::endl
	    << "  --format         use the specified file format for the input. Options are:"
	    << std::endl
	    << "                     lower-distance (lower triangular distance matrix; default)"
	    << std::endl
	    << "                     upper-distance (upper triangular distance matrix)" << std::endl
	    << "                     distance       (full distance matrix)" << std::endl
	    << "                     point-cloud    (point cloud in Euclidean space)" << std::endl
	    << "                     dipha          (distance matrix in DIPHA file format)" << std::endl
	    << "                     sparse         (sparse distance matrix in sparse triplet format)"
	    << std::endl
	    << "                     binary         (lower triangular distance matrix in binary format)"
	    << std::endl
	    << "  --dim <k>        compute persistent homology up to dimension k" << std::endl
	    << "  --threshold <t>  compute Rips complexes up to diameter t" << std::endl
#ifdef USE_COEFFICIENTS
	    << "  --modulus <p>    compute homology with coefficients in the prime field Z/pZ"
	    << std::endl
#endif
	    << "  --ratio <r>      only show persistence pairs with death/birth ratio > r" << std::endl
	    << std::endl;
	exit(exit_code);
}

int main(int argc, char** argv) {
	const char* filename = nullptr;

	file_format format = DISTANCE_MATRIX;

	cyc_index_t dim_max = 1;
	cyc_value_t threshold = std::numeric_limits<cyc_value_t>::max();
	float ratio = 1;
	cyc_coefficient_t modulus = 2;

	for (cyc_index_t i = 1; i < argc; ++i) {
		const std::string arg(argv[i]);
		if (arg == "--help") {
			print_usage_and_exit(0);
		} else if (arg == "--dim") {
			std::string parameter = std::string(argv[++i]);
			size_t next_pos;
			dim_max = std::stol(parameter, &next_pos);
			if (next_pos != parameter.size()) print_usage_and_exit(-1);
		} else if (arg == "--threshold") {
			std::string parameter = std::string(argv[++i]);
			size_t next_pos;
			threshold = std::stof(parameter, &next_pos);
			if (next_pos != parameter.size()) print_usage_and_exit(-1);
		} else if (arg == "--ratio") {
			std::string parameter = std::string(argv[++i]);
			size_t next_pos;
			ratio = std::stof(parameter, &next_pos);
			if (next_pos != parameter.size()) print_usage_and_exit(-1);
		} else if (arg == "--format") {
			std::string parameter = std::string(argv[++i]);
			if (parameter.rfind("lower", 0) == 0)
				format = LOWER_DISTANCE_MATRIX;
			else if (parameter.rfind("upper", 0) == 0)
				format = UPPER_DISTANCE_MATRIX;
			else if (parameter.rfind("dist", 0) == 0)
				format = DISTANCE_MATRIX;
			else if (parameter.rfind("point", 0) == 0)
				format = POINT_CLOUD;
			else if (parameter == "dipha")
				format = DIPHA;
			else if (parameter == "sparse")
				format = SPARSE;
			else if (parameter == "binary")
				format = BINARY;
			else
				print_usage_and_exit(-1);
#ifdef USE_COEFFICIENTS
		} else if (arg == "--modulus") {
			std::string parameter = std::string(argv[++i]);
			size_t next_pos;
			modulus = std::stol(parameter, &next_pos);
			if (next_pos != parameter.size() || !is_prime(modulus)) print_usage_and_exit(-1);
#endif
		} else {
			if (filename) { print_usage_and_exit(-1); }
			filename = argv[i];
		}
	}

	std::ifstream file_stream(filename);
	if (filename && file_stream.fail()) {
		std::cerr << "couldn't open file " << filename << std::endl;
		exit(-1);
	}

	if (format == SPARSE) {
		cyc_sparse_distance_matrix dist =
		    cyc_read_sparse_distance_matrix(filename ? file_stream : std::cin);
		// std::cout << "sparse distance matrix with " << dist.size() << " points and "
		//           << dist.num_edges << "/" << (dist.size() * (dist.size() - 1)) / 2 << " entries"
		//           << std::endl;

		cyc_ripser<cyc_sparse_distance_matrix>(std::move(dist), dim_max, threshold, ratio, modulus)
		    .cyc_compute_barcodes();
	} else {
		cyc_compressed_lower_distance_matrix dist =
		    read_file(filename ? file_stream : std::cin, format);

		cyc_value_t min = std::numeric_limits<cyc_value_t>::infinity(),
		        max = -std::numeric_limits<cyc_value_t>::infinity(), max_finite = max;
		int num_edges = 0;

		cyc_value_t enclosing_radius = std::numeric_limits<cyc_value_t>::infinity();
		if (threshold == std::numeric_limits<cyc_value_t>::max()) {
			for (size_t i = 0; i < dist.size(); ++i) {
				cyc_value_t r_i = -std::numeric_limits<cyc_value_t>::infinity();
				for (size_t j = 0; j < dist.size(); ++j) r_i = std::max(r_i, dist(i, j));
				enclosing_radius = std::min(enclosing_radius, r_i);
			}
		}

		for (auto d : dist.distances) {
			min = std::min(min, d);
			max = std::max(max, d);
			max_finite =
			    d != std::numeric_limits<cyc_value_t>::infinity() ? std::max(max, d) : max_finite;
			if (d <= threshold) ++num_edges;
		}
		// std::cout << "value range: [" << min << "," << max_finite << "]" << std::endl;

		if (threshold == std::numeric_limits<cyc_value_t>::max()) {
			// std::cout << "distance matrix with " << dist.size()
			//           << " points, using threshold at enclosing radius " << enclosing_radius
			//           << std::endl;
			cyc_ripser<cyc_compressed_lower_distance_matrix>(std::move(dist), dim_max, enclosing_radius,
			                                         ratio, modulus)
			    .cyc_compute_barcodes();
		} else {
			// std::cout << "sparse distance matrix with " << dist.size() << " points and "
			//           << num_edges << "/" << (dist.size() * dist.size() - 1) / 2 << " entries"
			//           << std::endl;

			cyc_ripser<cyc_sparse_distance_matrix>(cyc_sparse_distance_matrix(std::move(dist), threshold),
			                               dim_max, threshold, ratio, modulus)
			    .cyc_compute_barcodes();
		}
		exit(0);
	}
}


ripserResultsCycles rips_dm_cycles(float* D, int N, int modulus, int dim_max,
                      float threshold)
{
    // Setup distance matrix and figure out threshold
    std::vector<cyc_value_t> distances(D, D + N);
    cyc_compressed_lower_distance_matrix dist = cyc_compressed_lower_distance_matrix(
        cyc_compressed_upper_distance_matrix(std::move(distances)));

    // TODO: This seems like a dummy parameter at the moment
    float ratio = 1.0;

    cyc_value_t min = std::numeric_limits<cyc_value_t>::infinity(),
            max = -std::numeric_limits<cyc_value_t>::infinity(), max_finite = max;
    int num_edges = 0;

    /* Use enclosing radius when users does not set threshold or
     * when users uses infinity as a threshold
     */
    if (threshold == std::numeric_limits<cyc_value_t>::max() ||
        threshold == std::numeric_limits<cyc_value_t>::infinity()) {
        cyc_value_t enclosing_radius = std::numeric_limits<cyc_value_t>::infinity();
        for (size_t i = 0; i < dist.size(); ++i) {
            cyc_value_t r_i = -std::numeric_limits<cyc_value_t>::infinity();
            for (size_t j = 0; j < dist.size(); ++j)
                r_i = std::max(r_i, dist(i, j));
            enclosing_radius = std::min(enclosing_radius, r_i);
        }
        threshold = enclosing_radius;
    }

    for (auto d : dist.distances) {
        min = std::min(min, d);
        max = std::max(max, d);
        max_finite = d != std::numeric_limits<cyc_value_t>::infinity()
                         ? std::max(max, d)
                         : max_finite;
        if (d <= threshold)
            ++num_edges;
    }

    ripserResultsCycles res;
    if (threshold >= max) {
        cyc_ripser<cyc_compressed_lower_distance_matrix> r(
            std::move(dist), dim_max, threshold, ratio, modulus);
        r.cyc_compute_barcodes();
        r.cyc_copy_results(res);
    } else {
        cyc_ripser<cyc_sparse_distance_matrix> r(
            cyc_sparse_distance_matrix(std::move(dist), threshold), dim_max,
            threshold, ratio, modulus);
        r.cyc_compute_barcodes();
        r.cyc_copy_results(res);
    }
    res.num_edges = num_edges;
    return res;
}

ripserResultsCycles rips_dm_sparse_cycles(int* I, int* J, float* V, int NEdges, int N,
                             int modulus, int dim_max, float threshold)
{
    // TODO: This seems like a dummy parameter at the moment
    float ratio = 1.0;
    // Setup distance matrix and figure out threshold
    cyc_ripser<cyc_sparse_distance_matrix> r(
        cyc_sparse_distance_matrix(I, J, V, NEdges, N, threshold), dim_max, 
        threshold, ratio, modulus);
    r.cyc_compute_barcodes();
    // Report the number of edges that were added
    int num_edges = 0;
    for (int idx = 0; idx < NEdges; idx++) {
        if (I[idx] < J[idx] && V[idx] <= threshold) {
            num_edges++;
        }
    }
    ripserResultsCycles res;
    r.cyc_copy_results(res);
    res.num_edges = num_edges;
    return res;
}

#ifdef LIBRIPSER
int unpack_results(int** n_intervals, cyc_value_t** births_and_deaths,
                   int** cycle_length, int** cycles, cyc_index_t* dim_0_pairs, ripserResultsCycles res)
{
    int n_dims = res.births_and_deaths_by_dim.size();
    *n_intervals = (int*) malloc(n_dims * sizeof(int));
    int n_intervals_total = 0;

    for (int d = 0; d < n_dims; d++) {
        int n_int_d = res.births_and_deaths_by_dim[d].size() / 2;
        (*n_intervals)[d] = n_int_d;
        n_intervals_total += n_int_d;
    }
    *births_and_deaths =
        (cyc_value_t*) malloc(n_intervals_total * 2 * sizeof(cyc_value_t));
    *cycle_length = (int*) calloc(n_intervals_total, sizeof(int));

    int cycle_length_total = 0;
    int idx = 0;
    for (int d = 0; d < n_dims; d++) {
        std::copy(res.births_and_deaths_by_dim[d].begin(),
                  res.births_and_deaths_by_dim[d].end(),
                  &(*births_and_deaths)[2 * idx]);

        if (!res.cocycles_by_dim[d].empty()) {
            for (int i = 0; i < (*n_intervals)[d]; i++) {
                int cc_length = res.cocycles_by_dim[d][i].size();
                (*cycle_length)[idx] = cc_length;
                cycle_length_total += cc_length;
                idx++;
            }
        } else {
            idx += (*n_intervals)[d];
        }
    }

	*dim_0_pairs = (cyc_index_t*) calloc(n_intervals_total * 2 * sizeof(cyc_index_t));
	
	if(!res.cyc_dim_0_pairs.empty()) {
		for (int i =0; i < n_intervals_total * 2; i++) {
			std::copy(res.cyc_dim_0_pairs[i], &(*dim_0_pairs)[i]);
		}
	}

    if (do_cocycles && cycle_length_total > 0) {
        *cocycles = (int*) calloc(cycle_length_total, sizeof(int));

        int pos = 0;
        for (int d = 0; d < n_dims; d++) {
            if (!res.cocycles_by_dim[d].empty()) {
                for (int i = 0; i < (*n_intervals)[d]; i++) {
                    int cc_length = res.cocycles_by_dim[d][i].size();
                    std::copy(res.cocycles_by_dim[d][i].begin(),
                              res.cocycles_by_dim[d][i].end(),
                              &(*cocycles)[pos]);
                    pos += cc_length;
                }
            }
        }
    }
    return res.num_edges;
}

extern "C" {
#include "ripser.h"

/*
  C interface to Ripser.

  Results are passed through output arguments. The arrays are allocated in this
  function and have to be freed manually by the caller.

  Output arguments:
  * n_intervals: number of intervals per dimension. (length = dim_max + 1)
  * births_and_deaths: births and deaths of all dimension in a flat array.
  (length = 2 * sum(n_intervals))
  * cocycle_length: lengths of individual cocycles. (length = sum(n_intervals))
  * cocycles: cocycles stored in a flat array. (length = sum(cocycle_length))
  Input arguments:
  * D: lower triangle of the distance matrix in a flat array.
  * N: length of D.
  * modulus: Compute homology with coefficients in the prime field Z/pZ. p must
  be a prime number.
  * dim_max: Compute persistent homology up to this dimension
  * threshold: Compute Rips complexes up to this diameter
  * do_cocycles: If nonzero, calculate cocycles and write them to cocycle_length
  and cocycles.

  Returns number of edges.
*/
int c_rips_dm_cycles(int** n_intervals, cyc_value_t** births_and_deaths,
              int** cocycle_length, int** cocycles, int* dim_0_pairs cyc_value_t* D, int N,
              int modulus, int dim_max, cyc_value_t threshold)
{
    ripserResultsCycles res = rips_dm_cycles(D, N, modulus, dim_max, threshold);
    return unpack_results(n_intervals, births_and_deaths, cocycle_length,
                          cocycles, dim_0_pairs, res);
}

/*
  Same as c_rips_dm, but takes sparse matrix as input.

  Arguments:
  * I, J, V: indices and values.
  * NEdges: total number of indices and values.
  * N: size of sparse matrix.
*/
int c_rips_dm_sparse_cycles(int** n_intervals, cyc_value_t** births_and_deaths,
                     int** cocycle_length, int** cocycles, int* dim_0_pairs, int* I, int* J,
                     float* V, int NEdges, int N, int modulus, int dim_max,
                     float threshold)
{
    ripserResultsCycles res = rips_dm_sparse_cycles(I, J, V, NEdges, N, modulus, dim_max,
                                       threshold);
    return unpack_results(n_intervals, births_and_deaths, cocycle_length,
                          cocycles, dim_0_pairs, res);
}
}

#endif
